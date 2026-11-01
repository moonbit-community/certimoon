// Sequencing: a run of APPEND(es1, es2) runs es1 to values (or traps),
// then es2 on top of them.
//
// - reduce_app: a step of es1 is a step of APPEND(es1, es2) (the context
//   rule with LBase(NIL, es2));
// - reduce_append (package wasm): a step of APPEND(es1, es2), es1 not
//   all values, is a step of es1, or es1 has a trap at the top;
// - a trap at the top steps to [Trap], which is never safe for a step
//   more (trap_step, safe_trap);
// - safe_seq, by induction on n, and from it triple_seq and sl_seq.

///|
fn prove_sequencing() -> Unit raise {
  let safe = thm("safe")
  let reduce_rules = @bool.conjuncts_rule(@wasm.thm("reduce_rules")).to_array()
  let simple_rules = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let lfilled_nil = @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
    @bool.spec(tm("(NIL : List[Value])"), @wasm.thm("lfilled_base")),
  )
  let reduce_app = lemma(
    "reduce_app",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e1 : List[Einstr], reduce(s, f, es1, s2, f2, e1) → reduce(s, f, APPEND(es1, es2), s2, f2, APPEND(e1, es2))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(reduce_rules[38]),
      @meson.asm_meson_tac(ths([lfilled_nil])),
    ]),
  )
  let trap_step = lemma(
    "trap_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], trap_top(es) && !(es == [Trap]) → reduce(s, f, es, s, f, [Trap])",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(reduce_rules[0]),
      @tactics.match_mp_tac(simple_rules[38]),
      @simp.asm_rewrite_tac(ths([@wasm.thm("lfilled_trap_iff")])),
    ]),
  )
  let einstr = @ind_types.distinctness("einstr")
  let safe_trap = lemma(
    "safe_trap",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, !safe(SUC(n), s, f, [Trap], q)",
    @simp.rewrite_tac(
      ths([
        safe,
        @wasm.thm("reduce_not_trap"),
        @wasm.thm("map_v_to_e_cons"),
        @wasm.thm("eq_v_to_e"),
        einstr,
        @equal.gsym(einstr),
      ]),
    ),
  )
  let _ = lemma(
    "safe_seq",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{assn}, ∀ r : \{assn}, safe(n, s, f, es1, q) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, q(s, f, vs) → safe(m, s, f, APPEND(MAP(v_to_e, vs), es2), r)) → safe(n, s, f, APPEND(es1, es2), r)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safe])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          // unfold safe in the premise only
          @tactics.conv_tac(
            @equal.rator_conv(@equal.rand_conv(@equal.rator_conv(@equal.rand_conv(@simp.pure_once_rewrite_conv(ths([safe])))))),
          ),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.orelse_tac(
            // es1 has ended: es2 runs on its values
            seq([subst_vars(), @meson.asm_meson_tac(ths([]))]),
            seq([
              @simp.rewrite_tac(ths([safe])),
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([reduce_app])),
                  seq([
                    @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                    @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                    @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                    @tactics.disch_tac,
                    have("!ALL(is_val, (es1 : List[Einstr]))", @meson.asm_meson_tac(ths([@wasm.thm("reduce_ok")]))),
                    have("!((es1 : List[Einstr]) == [Trap])", @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_trap")]))),
                    @tactics.mp_tac(
                      @bool.ispecl(
                        @list.List([
                          tm("(s : Wstore)"),
                          tm("(f : Wframe)"),
                          tm("(es1 : List[Einstr])"),
                          tm("(es2 : List[Einstr])"),
                          tm("(t1 : Wstore)"),
                          tm("(t2 : Wframe)"),
                          tm("(t3 : List[Einstr])"),
                        ]),
                        @wasm.thm("reduce_append"),
                      ),
                    ),
                    @simp.asm_rewrite_tac(ths([])),
                    @tactics.repeat_tac(@tactics.strip_tac),
                    @tactics.orelse_tac(
                      // es1 stepped: the induction hypothesis
                      seq([
                        subst_vars(),
                        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                        @tactics.exists_tac(tm("(q : \{assn})")),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      // a trap at the top of es1: es1 steps to [Trap]
                      seq([
                        have(
                          "safe((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{assn}))",
                          @meson.asm_meson_tac(ths([trap_step])),
                        ),
                        @tactics.undisch_tac(tm("safe((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{assn}))")),
                        @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
                        @simp.rewrite_tac(ths([safe, safe_trap])),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let triple = thm("triple")
  let triple_seq = lemma(
    "triple_seq",
    "∀ p : \{assn}, ∀ bs1 : List[B_e], ∀ q : \{assn}, ∀ bs2 : List[B_e], ∀ r : \{assn}, triple(p, bs1, q) && triple(q, bs2, r) → triple(p, APPEND(bs1, bs2), r)",
    seq([
      @simp.rewrite_tac(ths([triple, @lists.map_append(), @lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safe_seq")),
      @tactics.exists_tac(tm("(q : \{assn})")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_seq",
    "∀ p : \{sassn}, ∀ bs1 : List[B_e], ∀ q : \{sassn}, ∀ bs2 : List[B_e], ∀ r : \{sassn}, sl_triple(p, bs1, q) && sl_triple(q, bs2, r) → sl_triple(p, APPEND(bs1, bs2), r)",
    seq([@simp.rewrite_tac(ths([thm("sl_triple")])), @meson.meson_tac(ths([triple_seq]))]),
  )
}
