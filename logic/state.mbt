// Rules on exact states, for proofs that run straight-line code.
//
// st(v, l, R) is the assertion "the stack is v, the locals are l, and R
// holds of the globals and the heap". The st_ rules are the instruction
// rules for it, from st(...) to st(...), so consecutive steps glue with
// sl_seq once their stacks and locals are written out (EL, list_update,
// app_binop computed): `norm` does that. st_snoc_ex turns the "operands on
// top of vs0" preconditions of sl_br_if and sl_if into st form.
//
// sum_to and its lemmas are for example_sum.

///|
let rty : String = "(List[Value], Num, \{heap}) -> Bool"

///|
fn prove_state_rules() -> Unit raise {
  def(
    "st",
    "st((v : List[Value]), (l : List[Value]), (r : \{rty}), (vs : List[Value]), (lc : List[Value]), (gs : List[Value]), (ms : Num), (h : \{heap})) == (vs == v && lc == l && r(gs, ms, h))",
  )
  let st = thm("st")
  let _ = lemma(
    "st_snoc_ex",
    "∀ v : List[Value], ∀ x : Value, ∀ l : List[Value], ∀ r : \{rty}, ∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (∃ vs0 : List[Value], vs == APPEND(vs0, [x]) && st(v, l, r, vs0, lc, gs, ms, h)) == st(APPEND(v, [x]), l, r, vs, lc, gs, ms, h)",
    seq([@simp.rewrite_tac(ths([st])), @meson.meson_tac(ths([]))]),
  )
  let _ = lemma(
    "list_update_cons",
    "∀ h : A, ∀ t : List[A], ∀ k : Num, ∀ x : A, list_update(CONS(h, t), k, x) == (if k == 0 { CONS(x, t) } else { CONS(h, list_update(t, k - 1, x)) })",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(tm("(k : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(
        ths([
          @wasm.thm("list_update"),
          arith("∀ n : Num, !(SUC(n) == 0)"),
          arith("∀ n : Num, SUC(n) - 1 == n"),
        ]),
      ),
    ]),
  )
  // the st form of an instruction rule: sl_conseq from `base` (applied to
  // `args`, its frame p first), with the entailments by `ent`
  let ent = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([st])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let st_rule = (name : String, stmt : String, base : String, args : Array[String]) => {
    let inst = @bool.ispecl(@list.List(args.map(tm)), thm(base))
    let body = @kernel.concl(inst)
    let triple = if @basics.is_imp(body) { @kernel.rand(body) } else { body }
    let (_, parts) = @basics.strip_comb(triple)
    guard parts.to_array() is [p, _, q] else { raise Failure("st_rule: " + base) }
    lemma(
      name,
      stmt,
      seq([
        @tactics.repeat_tac(@tactics.strip_tac),
        @tactics.match_mp_tac(thm("sl_conseq")),
        @tactics.exists_tac(p),
        @tactics.exists_tac(q),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(@list.List([
          // the base rule (after its hypothesis, if it has one)
          solve(
            if @basics.is_imp(body) {
              seq([@tactics.match_mp_tac(inst), @simp.asm_rewrite_tac(ths([]))])
            } else {
              @tactics.accept_tac(inst)
            },
          ),
          solve(ent),
        ])),
      ]),
    )
  }
  let frame = "st((v : List[Value]), (l : List[Value]), (r : \{rty}))"
  let state = (v : String, l : String) => "st(\{v}, \{l}, r)"
  let vars = "∀ v : List[Value], ∀ l : List[Value], ∀ r : \{rty}"
  let _ = st_rule(
    "st_const",
    "\{vars}, ∀ c : V_num, sl_triple(\{state("v", "l")}, [EConstNum(c)], \{state("APPEND(v, [V_num(c)])", "l")})",
    "sl_const",
    [frame, "(c : V_num)"],
  )
  let _ = st_rule(
    "st_binop",
    "\{vars}, ∀ t : T_num, ∀ op : Binop, ∀ c1 : V_num, ∀ c2 : V_num, ∀ c : V_num, app_binop(op, c1, c2) == SOME(c) → sl_triple(\{state("APPEND(v, [V_num(c1), V_num(c2)])", "l")}, [Binop(t, op)], \{state("APPEND(v, [V_num(c)])", "l")})",
    "sl_binop",
    [frame, "(t : T_num)", "(op : Binop)", "(c1 : V_num)", "(c2 : V_num)", "(c : V_num)"],
  )
  let _ = st_rule(
    "st_testop",
    "\{vars}, ∀ t : T_num, ∀ op : Testop, ∀ c : V_num, sl_triple(\{state("APPEND(v, [V_num(c)])", "l")}, [Testop(t, op)], \{state("APPEND(v, [V_num(app_testop(op, c))])", "l")})",
    "sl_testop",
    [frame, "(t : T_num)", "(op : Testop)", "(c : V_num)"],
  )
  let _ = st_rule(
    "st_relop",
    "\{vars}, ∀ t : T_num, ∀ op : Relop, ∀ c1 : V_num, ∀ c2 : V_num, sl_triple(\{state("APPEND(v, [V_num(c1), V_num(c2)])", "l")}, [Relop(t, op)], \{state("APPEND(v, [V_num(app_relop(op, c1, c2))])", "l")})",
    "sl_relop",
    [frame, "(t : T_num)", "(op : Relop)", "(c1 : V_num)", "(c2 : V_num)"],
  )
  let _ = st_rule(
    "st_local_get",
    "\{vars}, ∀ k : Num, k < LENGTH(l) → sl_triple(\{state("v", "l")}, [Local_get(k)], \{state("APPEND(v, [EL(k, l)])", "l")})",
    "sl_local_get",
    [frame, "(k : Num)"],
  )
  let _ = st_rule(
    "st_local_set",
    "\{vars}, ∀ k : Num, ∀ c : V_num, k < LENGTH(l) → sl_triple(\{state("APPEND(v, [V_num(c)])", "l")}, [Local_set(k)], \{state("v", "list_update(l, k, V_num(c))")})",
    "sl_local_set",
    [frame, "(k : Num)", "(c : V_num)"],
  )
  // 1 + ... + n, and its steps as words
  def("sum_to", "sum_to(0) == 0 && sum_to(SUC(n)) == SUC(n) + sum_to(n)")
  let sum_to = thm("sum_to")
  let sum_suc = lemma(
    "sum_to_suc_word",
    "∀ m : Num, (word(sum_to(SUC(m))) : \{w32}) == word_add(word(SUC(m)), word(sum_to(m)))",
    @simp.rewrite_tac(ths([sum_to, @words.word_add_v1()])),
  )
  let _ = lemma(
    "sum_to_step",
    "∀ n : \{w32}, !(n == word(0)) → word(sum_to(val(n))) == word_add(n, word(sum_to(val(word_sub(n, word(1))))))",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      have(
        "1 <= val((n : \{w32}))",
        seq([
          @tactics.first_x_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([@equal.gsym(@words.val_eq_0())])),
          @meson.meson_tac(ths([arith("∀ x : Num, !(x == 0) → 1 <= x")])),
        ]),
      ),
      have(
        "SUC(val((n : \{w32})) - 1) == val(n)",
        @meson.asm_meson_tac(ths([arith("∀ x : Num, 1 <= x → SUC(x - 1) == x")])),
      ),
      @simp.rewrite_tac(ths([@words.val_word_sub_cases(), @words.val_word_1()])),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.mp_tac(@bool.spec(tm("val((n : \{w32})) - 1"), sum_suc)),
      @simp.asm_rewrite_tac(ths([@words.word_val()])),
    ]),
  )
  let _ = lemma(
    "sum_to_one_word",
    "word(sum_to(val((word(1) : \{w32})))) == (word(1) : \{w32})",
    seq([
      @simp.rewrite_tac(ths([@words.val_word_1()])),
      @simp.rewrite_tac(ths([arith("1 == SUC(0)"), sum_to, @arith.add_clauses()])),
    ]),
  )
  let _ = lemma(
    "sum_to_zero_word",
    "word(sum_to(val((word(0) : \{w32})))) == (word(0) : \{w32})",
    @simp.rewrite_tac(ths([@words.val_word_0(), sum_to])),
  )
}

///|
/// The rewrites `norm` writes states and side conditions out with.
fn norm_thms() -> Array[@kernel.Thm] raise {
  [
    @lists.append(),
    @lists.append_nil(),
    @equal.gsym(@lists.append_assoc()),
    @lists.el_cons(),
    @lists.length(),
    thm("list_update_cons"),
    @wasm.thm("app_binop"),
    @wasm.thm("app_binop_i_v"),
    @wasm.thm("app_binop_i"),
    @wasm.thm("map_option"),
    @wasm.thm("app_relop"),
    @wasm.thm("app_relop_i_v"),
    @wasm.thm("app_relop_i"),
    @wasm.thm("app_testop"),
    @wasm.thm("app_testop_i"),
    @wasm.thm("int_eqz"),
    thm("st_snoc_ex"),
    @class.eta_ax(),
  ]
}

///|
/// `th` with stacks, locals and instruction lists written out, and the
/// side conditions that are now numerals decided.
fn norm(th : @kernel.Thm) -> @kernel.Thm raise {
  let rw = @simp.rewrite_rule(ths(norm_thms()))
  let mut cur = th
  for _ in 0..<30 {
    let next = @equal.conv_rule(@calc_num.num_reduce_conv, rw(cur))
    if @basics.aconv(@kernel.concl(next), @kernel.concl(cur)) {
      return next
    }
    cur = next
  }
  raise Failure("wasmcert/logic: norm does not settle")
}
