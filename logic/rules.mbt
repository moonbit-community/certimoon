// Rules for single instructions, proved from the reduction relation.
//
// A rule's precondition puts the operands on top of a value stack vs0 of
// any length. Its proof needs every step of
// APPEND(MAP(v_to_e, vs0), operands ++ [x]) to be a step of
// operands ++ [x] with vs0 left alone (prefix_<name>): wasm's step_basic
// splits a step into values, a base step and the rest, and arity_<name>
// says the base step of x takes exactly its operands. step_cases then
// says what operands ++ [x] steps to.

///|
/// `tac`, then `split`, then `parts` on the goals `split` leaves.
fn then_split(
  tac : @tactics.Tactic,
  split : @tactics.Tactic,
  parts : Array[@tactics.Tactic],
) -> @tactics.Tactic {
  @tactics.then_tac(tac, @tactics.thenl(split, @list.List(parts)))
}

///|
/// The lemmas the instruction rules share.
fn prove_rule_lemmas() -> Unit raise {
  let _ = lemma(
    "snoc_eq",
    "∀ suf : List[A], ∀ x : A, ∀ l : List[A], APPEND(suf, [x]) == l == (!(l == NIL) && LAST(l) == x && suf == BUTLAST(l))",
    then_split(@tactics.repeat_tac(@tactics.gen_tac), @tactics.eq_tac, [
      seq([
        @tactics.disch_then(th => @tactics.subst1_tac(@equal.gsym(th))),
        @simp.rewrite_tac(
          ths([
            @lists.last_append(),
            @lists.butlast_append(),
            @lists.append_eq_nil(),
            @lists.not_cons_nil(),
            @lists.last(),
            @lists.butlast(),
            @lists.append_nil(),
          ]),
        ),
      ]),
      seq([
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        @tactics.match_mp_tac(@lists.append_butlast_last()),
        @simp.asm_rewrite_tac(ths([])),
      ]),
    ]),
  )
  let _ = lemma(
    "nil_eq_sym",
    "∀ l : List[A], (NIL == l) == (l == NIL)",
    @meson.meson_tac(ths([])),
  )
  let _ = lemma(
    "snoc_eq_sym",
    "∀ suf : List[A], ∀ x : A, ∀ l : List[A], l == APPEND(suf, [x]) == (!(l == NIL) && LAST(l) == x && suf == BUTLAST(l))",
    @meson.meson_tac(ths([thm("snoc_eq")])),
  )
  let _ = lemma(
    "no_trap",
    "∀ suf : List[Einstr], ∀ b : B_e, ∀ lh : Lholed, Lfilled(0, lh, [Trap], APPEND(suf, [Basic(b)])) && ALL(is_val, suf) → false",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "trap_top(APPEND((suf : List[Einstr]), [Basic((b : B_e))]))",
        @meson.asm_meson_tac(ths([@wasm.thm("lfilled_trap_iff")])),
      ),
      @tactics.undisch_tac(tm("trap_top(APPEND((suf : List[Einstr]), [Basic((b : B_e))]))")),
      @simp.rewrite_tac(ths([@wasm.thm("trap_top")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([tm("(vs : List[Value])"), tm("(suf : List[Einstr])"), tm("Basic((b : B_e))"), tm("Trap"), tm("(r : List[Einstr])")]),
          @wasm.thm("snoc_first_nonval"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([@wasm.thm("is_val_clauses"), @ind_types.distinctness("einstr")])),
    ]),
  )
  let _ = lemma(
    "no_trap_x",
    "∀ suf : List[Einstr], ∀ x : Einstr, ∀ lh : Lholed, Lfilled(0, lh, [Trap], APPEND(suf, [x])) && ALL(is_val, suf) && !(x == Trap) → false",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "trap_top(APPEND((suf : List[Einstr]), [(x : Einstr)]))",
        @meson.asm_meson_tac(ths([@wasm.thm("lfilled_trap_iff")])),
      ),
      @tactics.undisch_tac(tm("trap_top(APPEND((suf : List[Einstr]), [(x : Einstr)]))")),
      @simp.rewrite_tac(ths([@wasm.thm("trap_top")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([tm("(vs : List[Value])"), tm("(suf : List[Einstr])"), tm("(x : Einstr)"), tm("Trap"), tm("(r : List[Einstr])")]),
          @wasm.thm("snoc_first_nonval"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([@wasm.thm("is_val_clauses")])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "append_len_eq",
    "∀ a : List[A], ∀ b : List[A], ∀ c : List[A], ∀ d : List[A], APPEND(a, b) == APPEND(c, d) && LENGTH(b) == LENGTH(d) → a == c && b == d",
    seq([
      @simp.rewrite_tac(ths([@wasm.thm("append_split")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([
            @lists.length_append(),
            arith("∀ x : Num, ∀ y : Num, (x == y + x) == (y == 0)"),
            arith("∀ x : Num, ∀ y : Num, (y + x == x) == (y == 0)"),
            @lists.length_eq_nil(),
          ]),
        ),
      ),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.append(), @lists.append_nil()])),
    ]),
  )
  let star = thm("star")
  let _ = lemma(
    "star_pure",
    "∀ c : Bool, ∀ p : \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, star((h1 : \{heap}) => c && p(h1), r, h) == (c && star(p, r, h))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  let _ = lemma(
    "star_ex",
    "∀ q : (A) -> \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, star((h1 : \{heap}) => ∃ vs0 : A, q(vs0, h1), r, h) == (∃ vs0 : A, star(q(vs0), r, h))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  let _ = lemma(
    "all_suffix",
    "∀ p : (A) -> Bool, ∀ a : List[A], ∀ b : List[A], ∀ c : List[A], ∀ d : List[A], APPEND(a, b) == APPEND(c, d) && ALL(p, APPEND(a, b)) → ALL(p, d)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.then_tac(
        @tactics.mp_tac(@bool.conjunct2(th)),
        @tactics.subst1_tac(@bool.conjunct1(th)),
      )),
      @simp.rewrite_tac(ths([@lists.all_append()])),
      @tactics.disch_then(th => @tactics.accept_tac(@bool.conjunct2(th))),
    ]),
  )
}

///|
/// The rewrites that decide what a base step of APPEND(suf, [x]) can be,
/// x a written-out instruction.
let arity_rewrite : Ref[@equal.Conv?] = Ref::{ val: None }

///|
fn arity_conv(t : @kernel.Term) -> @kernel.Thm raise {
  let rw = match arity_rewrite.val {
    Some(c) => c
    None => {
      let facts = [
        thm("snoc_eq"),
        thm("snoc_eq_sym"),
        @lists.last(),
        @lists.butlast(),
        @lists.last_append(),
        @lists.butlast_append(),
        @lists.not_cons_nil(),
        @equal.gsym(@lists.not_cons_nil()),
        @lists.append_eq_nil(),
        @lists.append(),
        @lists.append_nil(),
        @lists.cons_11(),
        @lists.map(),
        @lists.map_eq_nil(),
        @wasm.thm("v_to_e"),
        @theorems.exists_or_thm(),
        @theorems.left_exists_and_thm(),
        @theorems.right_exists_and_thm(),
      ]
      for ty_name in ["einstr", "b_e", "value", "v_num", "lholed"] {
        let d = @ind_types.distinctness(ty_name)
        facts.push(d)
        facts.push(@equal.gsym(d))
        facts.push(@ind_types.injectivity(ty_name))
      }
      let c = @simp.rewrite_conv(ths(facts))
      arity_rewrite.val = Some(c)
      c
    }
  }
  let unwind = @equal.top_depth_conv(@ind_types.unwind_conv)
  let once = @equal.thenc(rw, unwind)
  let mut th = @kernel.refl(t)
  for _ in 0..<20 {
    let cur = @equal.rhs(@kernel.concl(th))
    let next = once(cur)
    if @basics.aconv(@equal.rhs(@kernel.concl(next)), cur) {
      return th
    }
    th = @kernel.trans(th, next)
  }
  raise Failure("wasmcert/logic: arity_conv does not settle")
}

///|
/// `lemma(name, stmt)` for an arity statement: rewrite its first premise
/// (a reduce_simple or reduce_base step) with the relation's cases, decide
/// which rules can apply, and count the operands; `lemmas` close the cases
/// that remain (the reduce_simple steps inside reduce_base, the trap).
fn prove_arity(
  name : String,
  rel : String,
  stmt : String,
  lemmas : Array[@kernel.Thm],
) -> @kernel.Thm raise {
  let cases = @wasm.thm(rel + "_cases")
  let premise = (c : @equal.Conv) => @equal.rator_conv(
    @equal.rand_conv(@equal.rator_conv(@equal.rand_conv(c))),
  )
  lemma(
    name,
    stmt,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.conv_tac(
        premise(@equal.thenc(@simp.pure_once_rewrite_conv(ths([cases])), arity_conv)),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.asm_rewrite_tac(ths([@lists.length()])),
      @tactics.try_tac(@int.arith_tac),
      @tactics.try_tac(@meson.asm_meson_tac(ths(lemmas))),
    ]),
  )
}

///|
/// The arity lemmas for instruction `x` (its variables declared in it)
/// with `n` operands: arity_simple_<name> and arity_<name>.
fn prove_arities(
  name : String,
  x : String,
  n : Int,
  trap? : Array[@kernel.Thm] = [],
) -> @kernel.Thm raise {
  // x's variables are free in the statements: generalize them
  let trap = if trap.is_empty() { [thm("no_trap")] } else { trap }
  let simple = prove_arity(
    "arity_simple_" + name,
    "reduce_simple",
    "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [\{x}]), e2) && ALL(is_val, suf) → LENGTH(suf) == \{n}",
    trap,
  )
  let simple = @bool.gen_all(simple)
  prove_arity(
    "arity_" + name,
    "reduce_base",
    "∀ s : Wstore, ∀ f : Wframe, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, APPEND(suf, [\{x}]), s2, f2, e2) && ALL(is_val, suf) → LENGTH(suf) == \{n}",
    [simple],
  )
}

///|
/// prefix_<name>: a step of the value stack vs0, then the operands `ops`
/// and the instruction `x`, is a step of ops and x with vs0 left alone.
fn prove_prefix(
  name : String,
  ops : Array[String],
  x : String,
  arity : @kernel.Thm,
) -> @kernel.Thm raise {
  let code = "[" + (ops + [x]).join(", ") + "]"
  let ops_t = if ops.is_empty() { "(NIL : List[Einstr])" } else { "[" + ops.join(", ") + "]" }
  let vals = [
    @lists.all_append(),
    @wasm.thm("all_vals_map"),
    @lists.all(),
    @wasm.thm("is_val_clauses"),
    @ind_types.distinctness("einstr"),
  ]
  let arity = @bool.gen_all(@tactics.prove(@kernel.concl(arity), @tactics.accept_tac(arity)))
  lemma(
    "prefix_" + name,
    "∀ vs0 : List[Value], ∀ s : Wstore, ∀ f : Wframe, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, APPEND(MAP(v_to_e, vs0), \{code}), s2, f2, es2) → (∃ e : List[Einstr], es2 == APPEND(MAP(v_to_e, vs0), e) && reduce(s, f, \{code}, s2, f2, e))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(s : Wstore)"),
            tm("(f : Wframe)"),
            tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), \{ops_t})"),
            tm(x),
            tm("(s2 : Wstore)"),
            tm("(f2 : Wframe)"),
            tm("(es2 : List[Einstr])"),
          ]),
          @wasm.thm("step_basic"),
        ),
      ),
      // APPEND(APPEND(vs0, ops), [x]) is the configuration's list
      @simp.rewrite_tac(ths([@equal.gsym(@lists.append_assoc()), @lists.append()])),
      @simp.asm_rewrite_tac(ths(vals)),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "ALL(is_val, (suf : List[Einstr]))",
        seq([
          @tactics.match_mp_tac(thm("all_suffix")),
          @tactics.exists_tac(tm("MAP(v_to_e, (vs0 : List[Value]))")),
          @tactics.exists_tac(tm(ops_t)),
          @tactics.exists_tac(tm("(pre : List[Einstr])")),
          @simp.asm_rewrite_tac(ths(vals)),
        ]),
      ),
      have(
        "LENGTH((suf : List[Einstr])) == \{ops.length()}",
        seq([@tactics.match_mp_tac(arity), @meson.asm_meson_tac(ths([]))]),
      ),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("MAP(v_to_e, (vs0 : List[Value]))"),
            tm(ops_t),
            tm("(pre : List[Einstr])"),
            tm("(suf : List[Einstr])"),
          ]),
          thm("append_len_eq"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([@lists.length()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      // NIL == suf as suf == NIL, so suf is substituted
      @simp.rewrite_tac(ths([thm("nil_eq_sym")])),
      @tactics.strip_tac,
      subst_vars(),
      @tactics.exists_tac(tm("(e' : List[Einstr])")),
      @simp.rewrite_tac(ths([])),
      @tactics.match_mp_tac(@wasm.thm("reduce_base_reduce")),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.append()]))),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}

///|
/// Rewrites that bring a lifted assertion `lift(p, r, s, f, vs)` with p
/// of the form `∃ vs0, vs == ... && q(vs0, ls, gs, h)` to its pure part and
/// a star.
fn lift_facts() -> Array[@kernel.Thm] {
  [thm("lift"), thm("star_ex"), thm("star_pure"), @class.eta_ax()]
}

///|
/// The rule `name` for a step of `ops ++ [x]` (each in the term syntax)
/// that leaves the store and frame alone and ends in one value:
/// `progress` proves the step exists (in the goal
/// ∃ s2 f2 es2. reduce(...) with the prefix vs0), `prefix` and
/// `cases` (step_cases on ops ++ [x]) say which steps there are, and
/// `result` is the value term. `facts` adds what the precondition implies
/// (before the cases on n), and `unfold` rewrites the assumptions and the
/// cases with the definitions step_cases computed with.
fn prove_value_rule(
  name : String,
  stmt : String,
  ops : Array[String],
  x : String,
  result : String,
  prefix : @kernel.Thm,
  cases : @kernel.Thm,
  progress : @tactics.Tactic,
  facts? : @tactics.Tactic = @tactics.all_tac,
  unfold? : Array[@kernel.Thm] = [],
) -> @kernel.Thm raise {
  let code = "[" + (ops + [x]).join(", ") + "]"
  let step = "[Basic(EConstNum(\{result}))]"
  let lfill = @wasm.thm("lfill")
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  lemma(
    name,
    stmt,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      // the precondition: the memory, the stack and the frame's assertion
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      facts,
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), @wasm.thm("v_to_e"), @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(tm("(s : Wstore)")),
            @tactics.exists_tac(tm("(f : Wframe)")),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), \{step})")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([
                  tm("(s : Wstore)"),
                  tm("(f : Wframe)"),
                  tm("LBase((vs0 : List[Value]), NIL)"),
                  tm(code),
                  tm("(s : Wstore)"),
                  tm("(f : Wframe)"),
                  tm(step),
                ]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            progress,
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(@bool.gen_all(prefix))(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths(unfold))),
            @simp.asm_rewrite_tac(ths(opt + unfold)),
            // the case's memory is the precondition's: unwind, rewrite again
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @simp.asm_rewrite_tac(ths(opt + unfold)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([@equal.gsym(@wasm.thm("v_to_e")), thm("map_snoc")])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts() + unfold)),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.exists_tac(tm("(vs0 : List[Value])")),
            @simp.asm_rewrite_tac(ths(unfold)),
          ]),
        ]),
      ),
    ]),
  )
}

///|
fn prove_rules() -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let rb_lift = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  // binary operators
  let binop = "Basic(Binop((t : T_num), (op : Binop)))"
  let consts = ["Basic(EConstNum((c1 : V_num)))", "Basic(EConstNum((c2 : V_num)))"]
  let arity = prove_arities("binop", binop, 2)
  let prefix = prove_prefix("binop", consts, binop, arity)
  let cases = @wasm.step_cases(s, f, tm("[" + (consts + [binop]).join(", ") + "]"))
  let _ = prove_value_rule(
    "sl_binop",
    "∀ p : \{sassn}, ∀ t : T_num, ∀ op : Binop, ∀ c1 : V_num, ∀ c2 : V_num, ∀ c : V_num, app_binop(op, c1, c2) == SOME(c) → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(c1), V_num(c2)]) && p(vs0, ls, gs, h)), [Binop(t, op)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(c)]) && p(vs0, ls, gs, h)))",
    consts,
    binop,
    "(c : V_num)",
    prefix,
    cases,
    @meson.asm_meson_tac(ths([rb_lift, rs[1]])),
  )
  // i32.load
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let k = "Basic(EConstNum(ConstInt32((k : \{w32}))))"
  let load = "Basic(Load(T_i32, NONE, (a : Num), (off : Num)))"
  let arity = prove_arities("load", "Basic(Load((t : T_num), (sx : Option[(Tp_num, Sx)]), (a : Num), (off : Num)))", 1)
  let prefix = prove_prefix("load", [k], load, arity)
  let cases = @wasm.step_cases(s, f, tm("[\{k}, \{load}]"))
  let mem = "EL((j : Num), s_mems((s : Wstore)))"
  let bs = "(bs : List[\{w8}])"
  let frame = "star((p : \{sassn})((vs0 : List[Value]), f_locs((f : Wframe)), gvals((s : Wstore), (f : Wframe))), (r : \{hprop}))"
  let unfold = ["smem_ind", "load", "read_bytes", "mem_length", "deserialise_i32", "t_num_length"].map(@wasm.thm)
  let _ = prove_value_rule(
    "sl_load_i32",
    "∀ p : \{sassn}, ∀ k : \{w32}, ∀ a : Num, ∀ off : Num, ∀ bs : List[\{w8}], LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k))]) && star(pts(val(k) + off, bs), p(vs0, ls, gs), h)), [Load(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(deserialise_i32(bs)))]) && star(pts(val(k) + off, bs), p(vs0, ls, gs), h)))",
    [k],
    load,
    "wasm_deserialise_num(\{bs}, T_i32)",
    prefix,
    cases,
    seq([
      @tactics.match_mp_tac(rb[12]),
      @tactics.exists_tac(tm("(j : Num)")),
      @tactics.exists_tac(tm(mem)),
      @simp.asm_rewrite_tac(ths([@wasm.thm("t_num_length")])),
    ]),
    facts=have(
      "load(\{mem}, val((k : \{w32})), (off : Num), 4) == SOME(\{bs})",
      seq([
        @tactics.mp_tac(
          @bool.ispecl(
            @list.List([tm(mem), tm("val((k : \{w32}))"), tm("(off : Num)"), tm(bs), tm(frame)]),
            thm("load_pts"),
          ),
        ),
        @simp.rewrite_tac(ths([@equal.gsym(thm("star_assoc")), @equal.gsym(@lists.length_eq_nil())])),
        @simp.asm_rewrite_tac(ths([])),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @simp.rewrite_tac(ths([])),
      ]),
    ),
    unfold~,
  )
  prove_store_rule(rb, k, lift_facts(), [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ])
}

///|
/// i32.store, and what it needs about the store and its memories.
fn prove_store_rule(
  rb : Array[@kernel.Thm],
  k : String,
  lift_facts : Array[@kernel.Thm],
  opt : Array[@kernel.Thm],
) -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let list_update = @wasm.thm("list_update")
  let list_defs = [list_update, @lists.length(), @lists.el(), @lists.hd(), @lists.tl(), @arith.lt_suc(), @arith.lt()]
  let by_induction = seq([
    @lists.list_induct_tac,
    @tactics.gen_tac,
    @tactics.struct_cases_tac(@bool.spec(tm("(i : Num)"), @nums.num_cases())),
    @simp.asm_rewrite_tac(ths(list_defs)),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let length_update = lemma(
    "length_list_update",
    "∀ l : List[A], ∀ i : Num, ∀ x : A, LENGTH(list_update(l, i, x)) == LENGTH(l)",
    by_induction,
  )
  let el_update = lemma(
    "el_list_update",
    "∀ l : List[A], ∀ i : Num, ∀ x : A, i < LENGTH(l) → EL(i, list_update(l, i, x)) == x",
    by_induction,
  )
  let mems_update = lemma(
    "s_mems_update_get",
    "∀ v : List[\{mem_ty}], ∀ s : Wstore, s_mems(s_mems_update(v, s)) == v",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(s, @ind_types.cases("wstore"))),
      @simp.rewrite_tac(ths([@wasm.thm("s_mems_update"), @wasm.thm("s_mems")])),
    ]),
  )
  // writing memory leaves the globals alone
  let globs_mems = lemma(
    "s_globs_mems_update",
    "∀ v : List[\{mem_ty}], ∀ s : Wstore, s_globs(s_mems_update(v, s)) == s_globs(s)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(s, @ind_types.cases("wstore"))),
      @simp.rewrite_tac(ths([@wasm.thm("s_mems_update"), @wasm.thm("s_globs")])),
    ]),
  )
  let gvals_mems = lemma(
    "gvals_mems_update",
    "∀ v : List[\{mem_ty}], ∀ s : Wstore, ∀ f : Wframe, gvals(s_mems_update(v, s), f) == gvals(s, f) && (globs_ok(s_mems_update(v, s), f) == globs_ok(s, f))",
    @simp.rewrite_tac(ths([thm("gvals"), thm("globs_ok"), globs_mems])),
  )
  let serialise_len = lemma(
    "serialise_i32_length",
    "∀ v : \{w32}, LENGTH(serialise_i32(v)) == 4",
    @simp.rewrite_tac(
      ths([
        @wasm.thm("serialise_i32"),
        arith("4 == SUC(SUC(SUC(SUC(0))))"),
        @wasm.thm("le_bytes"),
        @lists.length(),
      ]),
    ),
  )
  let v = "Basic(EConstNum(ConstInt32((v : \{w32}))))"
  let store = "Basic(Store(T_i32, NONE, (a : Num), (off : Num)))"
  let code = "[\{k}, \{v}, \{store}]"
  let arity = prove_arities("store", "Basic(Store((t : T_num), (tp : Option[Tp_num]), (a : Num), (off : Num)))", 2)
  let prefix = prove_prefix("store", [k, v], store, arity)
  let cases = @wasm.step_cases(s, f, tm(code), compute=false)
  let mem = "EL((j : Num), s_mems((s : Wstore)))"
  let bytes = "serialise_i32((v : \{w32}))"
  let written = "write_bytes(\{mem}, val((k : \{w32})) + (off : Num), \{bytes})"
  let updated = "s_mems_update(list_update(s_mems((s : Wstore)), (j : Num), \{written}), s)"
  let frame = "star((p : \{sassn})((vs0 : List[Value]), f_locs((f : Wframe)), gvals((s : Wstore), (f : Wframe))), (r : \{hprop}))"
  let defs = ["typeof_num", "bits_num", "t_num_length"].map(@wasm.thm)
  let _ = lemma(
    "sl_store_i32",
    "∀ p : \{sassn}, ∀ k : \{w32}, ∀ a : Num, ∀ off : Num, ∀ v : \{w32}, ∀ bs : List[\{w8}], LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k)), V_num(ConstInt32(v))]) && star(pts(val(k) + off, bs), p(vs0, ls, gs), h)), [Store(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == vs0 && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls, gs), h)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      // the store succeeds, and the bytes are there after it
      have(
        "store(\{mem}, val((k : \{w32})), (off : Num), \{bytes}, 4) == SOME(\{written}) && star(pts(val(k) + off, \{bytes}), \{frame}, heap_of(\{written}))",
        seq([
          @tactics.mp_tac(
            @bool.ispecl(
              @list.List([tm(mem), tm("val((k : \{w32}))"), tm("(off : Num)"), tm("(bs : List[\{w8}])"), tm(bytes), tm(frame)]),
              thm("store_pts"),
            ),
          ),
          @simp.rewrite_tac(ths([@equal.gsym(thm("star_assoc")), @equal.gsym(@lists.length_eq_nil()), serialise_len])),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @simp.rewrite_tac(ths([])),
        ]),
      ),
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), @wasm.thm("v_to_e"), @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(tm(updated)),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("MAP(v_to_e, (vs0 : List[Value]))")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs0 : List[Value]), NIL)"), tm(code), tm(updated), f, tm("(NIL : List[Einstr])")]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([@wasm.thm("lfill"), @lists.append(), @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(rb[16]),
            @tactics.exists_tac(tm(mem)),
            @simp.asm_rewrite_tac(ths(defs)),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(@bool.gen_all(prefix))(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.asm_rewrite_tac(ths(opt + defs)),
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @simp.asm_rewrite_tac(ths(opt + defs)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([@lists.append_nil()])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts + [mems_update, length_update, gvals_mems])),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_simp_tac(ths([el_update])),
            @simp.rewrite_tac(ths([thm("star_assoc")])),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}

