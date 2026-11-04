// Rules for br_if and if.
//
// Both take an i32 condition c and step once: br_if to br i (c ≠ 0) or to
// nothing (c = 0), and if to a block of its first (c ≠ 0) or second
// (c = 0) branch. So each rule asks for what the configuration becomes:
// sl_br_if for a triple of br i (sl_br gives one) and that p entails q,
// and sl_if for a triple of each block (sl_block gives one). sl_if holds
// for any block type; sl_block's limit to Tbv(ot) is sl_block's own.

///|
/// `sl_br_if` or `sl_if`: from a precondition with the condition c on top
/// of vs0, the instruction `x` steps to `zero` (c = 0) or `nonzero`, by
/// the reduce_simple rules `rule0` and `rule1`; the hypotheses (rewritten,
/// with the frame r) say each continuation is safe, `if_zero` and
/// `if_nonzero` finish each case from them.
fn prove_conditional(
  name : String,
  stmt : String,
  x : String,
  zero : String,
  nonzero : String,
  rule0 : @kernel.Thm,
  rule1 : @kernel.Thm,
  if_zero : @tactics.Tactic,
  if_nonzero : @tactics.Tactic,
) -> @kernel.Thm raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let c = "Basic(EConstNum(ConstInt32((c : \{w32}))))"
  let code = "[\{c}, \{x}]"
  let arity = prove_arities(name.replace(old="sl_", new=""), x, 1)
  let prefix = @bool.gen_all(prove_prefix(name.replace(old="sl_", new=""), [c], x, arity))
  let cases = @wasm.step_cases(s, f, tm(code), compute=false)
  let rb_lift = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let lfill = @wasm.thm("lfill")
  let vs0 = "(vs0 : List[Value])"
  // the step to `out`, by `rule`
  let progress = (out : String, rule : @kernel.Thm) => seq([
    @tactics.exists_tac(s),
    @tactics.exists_tac(f),
    @tactics.exists_tac(tm("APPEND(MAP(v_to_e, \{vs0}), \{out})")),
    @tactics.mp_tac(
      @bool.ispecl(
        @list.List([s, f, tm("LBase(\{vs0}, NIL)"), tm(code), s, f, tm(out)]),
        @wasm.thm("decomp_reduce"),
      ),
    ),
    @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
    @tactics.disch_then(th => @tactics.match_mp_tac(th)),
    @tactics.match_mp_tac(rb_lift),
    @tactics.match_mp_tac(rule),
    @simp.asm_rewrite_tac(ths([])),
  ])
  // every step is to `out`; then `finish`
  let steps = (finish : @tactics.Tactic) => seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
    subst_vars(),
    @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.rewrite_tac(ths([@lists.append_nil()])),
    finish,
  ])
  lemma(
    name,
    stmt,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_l"), thm("triple_l"), @lists.map()])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.x_gen_tac(tm("(r : \{hprop})")),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      // p holds of vs0, below the condition
      have(
        "lift((p : \{sassn}), (r : \{hprop}), (s : Wstore), (f : Wframe), \{vs0})",
        seq([
          @simp.rewrite_tac(ths([thm("lift")])),
          @tactics.exists_tac(tm("(j : Num)")),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), @wasm.thm("v_to_e"), @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safel")])),
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(c : \{w32}) == word(0)")),
        @list.List([
          @tactics.thenl(@tactics.conj_tac, @list.List([progress(zero, rule0), steps(if_zero)])),
          @tactics.thenl(@tactics.conj_tac, @list.List([progress(nonzero, rule1), steps(if_nonzero)])),
        ]),
      ),
    ]),
  )
}

///|
fn prove_conditional_rules() -> Unit raise {
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let sa = sassn
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(c))]) && p(vs0, lc, gs, h))"
  // the continuation is safe by the hypothesis for its case
  let by_hypothesis = @meson.asm_meson_tac(ths([]))
  let _ = prove_conditional(
    "sl_br_if",
    "∀ p : \{sa}, ∀ q : \{sa}, ∀ ls : List[\{sa}], ∀ i : Num, ∀ c : \{w32}, (!(c == word(0)) → sl_triple_l(p, [Br(i)], q, ls)) && (c == word(0) → (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ h : \{heap}, p(vs, lc, gs, h) → q(vs, lc, gs, h))) → sl_triple_l(\{pre}, [Br_if(i)], q, ls)",
    "Basic(Br_if((i : Num)))",
    "(NIL : List[Einstr])",
    "[Basic(Br((i : Num)))]",
    rs[30],
    rs[31],
    // c = 0: vs0 is the result, and p entails q
    seq([
      @tactics.match_mp_tac(thm("safel_vals")),
      @tactics.match_mp_tac(thm("lift_mono")),
      @tactics.exists_tac(tm("(p : \{sa})")),
      @tactics.exists_tac(tm("(vs0 : List[Value])")),
      @meson.asm_meson_tac(ths([])),
    ]),
    by_hypothesis,
  )
  let _ = prove_conditional(
    "sl_if",
    "∀ p : \{sa}, ∀ q : \{sa}, ∀ ls : List[\{sa}], ∀ tb : Tb, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ c : \{w32}, (!(c == word(0)) → sl_triple_l(p, [Block(tb, bs1)], q, ls)) && (c == word(0) → sl_triple_l(p, [Block(tb, bs2)], q, ls)) → sl_triple_l(\{pre}, [If(tb, bs1, bs2)], q, ls)",
    "Basic(If((tb : Tb), (bs1 : List[B_e]), (bs2 : List[B_e])))",
    "[Basic(Block((tb : Tb), (bs2 : List[B_e])))]",
    "[Basic(Block((tb : Tb), (bs1 : List[B_e])))]",
    rs[25],
    rs[26],
    by_hypothesis,
    by_hypothesis,
  )
}
