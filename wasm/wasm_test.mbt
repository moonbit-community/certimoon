// Checks of the WasmCert port: it adds no axioms, each relation has as
// many rules as Isabelle's, no rule quantifies over a misspelt constant,
// and small computations and derivations go through.

///|
fn rule_list(name : String) -> Array[@kernel.Term] {
  @basics.conjuncts(@kernel.concl(@wasm.thm(name + "_rules"))).to_array()
}

///|
test "adds no axioms" {
  @wasm.load()
  @testkit.check_axioms()
}

///|
test "each relation has as many rules as in Isabelle" {
  let counts = [
    ("b_e_typing", 59),
    ("ref_typing", 3),
    ("v_typing", 3),
    ("inst_typing", 1),
    ("frame_typing", 1),
    ("cl_typing", 2),
    ("e_typing", 9),
    ("store_typing", 1),
    ("config_typing", 1),
    ("reduce_simple", 39),
    ("reduce", 62),
    ("store_extension", 1),
    ("Lfilled", 2),
    ("Lfilled_exact", 2),
    ("reduce_trans", 2),
    ("reduce_irrtrans", 2),
  ]
  for p in counts {
    assert_eq((p.0, rule_list(p.0).length()), p)
  }
}

///|
/// A misspelt constant in a rule would be read as a variable and
/// quantified: such a variable is applied (a function) or capitalised.
test "rules quantify only over variables" {
  for
    name in [
      "b_e_typing", "ref_typing", "v_typing", "inst_typing", "frame_typing", "cl_typing",
      "e_typing", "store_typing", "config_typing", "reduce_simple", "reduce", "store_extension",
      "Lfilled", "Lfilled_exact", "reduce_trans", "reduce_irrtrans",
    ] {
    for rule in rule_list(name) {
      let (vars, _) = @basics.strip_forall(rule)
      for v in vars {
        let (n, t) = @kernel.dest_var(v)
        let is_fun = !@kernel.is_vartype(t) && @kernel.dest_type(t).0 == "fun"
        let capital = n.to_array()[0] is ('A'..='Z')
        if is_fun || (capital && n != "C" && n != "LI") {
          fail("\{name}: suspicious variable \{n}")
        }
      }
    }
  }
}

///|
/// Proves `goal` by rewriting with the named definitions (and `extra`)
/// and evaluating word and numeral arithmetic, in a few rounds.
fn compute(
  goal : String,
  defs : Array[String],
  extra? : Array[@kernel.Thm] = [],
) -> @kernel.Thm raise {
  let ths = @list.List(defs.map(@wasm.thm) + extra)
  let step = @tactics.then_tac(
    @simp.rewrite_tac(ths),
    @tactics.then_tac(
      @tactics.conv_tac(@words.word_reduce_conv),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ),
  )
  // a fixed number of rounds: the steps never fail, so REPEAT would not stop
  @tactics.prove(
    @term_syntax.parse_term(goal),
    @tactics.then_tac(step, @tactics.then_tac(step, step)),
  )
}

///|
test "definitions compute" {
  let add = compute(
    "app_binop(Binop_i(Add), ConstInt32(word(2)), ConstInt32(word(3))) == SOME(ConstInt32(word(5)))",
    ["app_binop", "app_binop_i_v", "app_binop_i", "map_option"],
  )
  inspect(
    @term_syntax.print_term(@kernel.concl(add)),
    content=(
      #|app_binop(Binop_i(Add), ConstInt32(word(2)), ConstInt32(word(3))) == SOME(ConstInt32(word(5)))
    ),
  )
  // INT_MIN / -1 overflows: no result (Isabelle's int_div_s)
  ignore(
    compute(
      "app_binop(Binop_i(Div(S)), ConstInt32(word(2147483648)), ConstInt32(word_not(word(0)))) == NONE",
      ["app_binop", "app_binop_i_v", "app_binop_i", "int_div_s", "map_option"],
      extra=[@words.dimindex_32()],
    ),
  )
  // little-endian bytes
  ignore(
    compute(
      "serialise_i32(word(258)) == [word(2), word(1), word(0), word(0)]",
      ["serialise_i32", "le_bytes"],
      extra=[@int.arith_rule(@term_syntax.parse_term("4 == SUC(SUC(SUC(SUC(0))))"))],
    ),
  )
  ignore(compute("deserialise_i32([word(2), word(1)]) == word(258)", [
    "deserialise_i32", "num_of_bytes",
  ]))
}

///|
test "a reduction step and a typing derivation" {
  let add = compute(
    "app_binop(Binop_i(Add), ConstInt32(word(2)), ConstInt32(word(3))) == SOME(ConstInt32(word(5)))",
    ["app_binop", "app_binop_i_v", "app_binop_i", "map_option"],
  )
  let step = @tactics.prove(
    @term_syntax.parse_term(
      "reduce_simple([Basic(EConstNum(ConstInt32(word(2)))), Basic(EConstNum(ConstInt32(word(3)))), Basic(Binop(T_i32, Binop_i(Add)))], [Basic(EConstNum(ConstInt32(word(5))))])",
    ),
    @meson.meson_tac(@list.List([@wasm.thm("reduce_simple_rules"), add])),
  )
  ignore(step)
  let typed = @tactics.prove(
    @term_syntax.parse_term(
      "∀ C : T_context, b_e_typing(C, [EConstNum(ConstInt32(word(1)))], Tf(NIL, [T_num(T_i32)]))",
    ),
    @meson.meson_tac(
      @list.List([@wasm.thm("b_e_typing_rules"), @wasm.thm("typeof_num")]),
    ),
  )
  ignore(typed)
}

///|
test "rules read as in Isabelle" {
  let show = (name : String, i : Int) => @term_syntax.print_term(rule_list(name)[i])
  // Isabelle: block
  inspect(show("b_e_typing", 23), content=(
    #|∀ C : T_context, ∀ tb : Tb, ∀ es : List[B_e], ∀ tn : List[Valtype], ∀ tm : List[Valtype], tb_tf_t(C, tb) == SOME(Tf(tn, tm)) && b_e_typing(ctx_label_update(CONS(tm, ctx_label(C)), C), es, Tf(tn, tm)) → b_e_typing(C, [Block(tb, es)], Tf(tn, tm))
  ))
  // Isabelle: label
  inspect(show("reduce", 38), content=(
    #|∀ es : List[Einstr], ∀ k : Num, ∀ lholed : Lholed, ∀ es' : List[Einstr], ∀ s : Wstore, ∀ f : Wframe, ∀ les : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, es, s', f', es') && Lfilled(k, lholed, es, les) && Lfilled(k, lholed, es', les') → reduce(s, f, les, s', f', les')
  ))
}
