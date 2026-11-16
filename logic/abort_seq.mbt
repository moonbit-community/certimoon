// A nontrapping prefix can lead to either normal completion or a specified abort.

///|
fn prove_abort_sequencing() -> Unit raise {
  let safe = thm("safe")
  let sa = thm("safe_abort")
  let reduce_app = thm("reduce_app")
  let trap_step = thm("trap_step")
  let safe_trap = thm("safe_trap")
  let _ = lemma(
    "safe_abort_seq",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{assn}, ∀ r : \{assn}, ∀ a : (Wstore,Wframe) -> Bool, safe(n, s, f, es1, q) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, q(s, f, vs) → safe_abort(m, s, f, APPEND(MAP(v_to_e, vs), es2), r, a)) → safe_abort(n, s, f, APPEND(es1, es2), r, a)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([sa])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          // unfold safe in the premise only
          @tactics.conv_tac(
            @equal.rator_conv(
              @equal.rand_conv(
                @equal.rator_conv(
                  @equal.rand_conv(@simp.pure_once_rewrite_conv(ths([safe]))),
                ),
              ),
            ),
          ),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.orelse_tac(
            // es1 has ended: es2 runs on its values
            seq([subst_vars(), @meson.asm_meson_tac(ths([]))]),
            seq([
              @simp.rewrite_tac(ths([sa])),
              @tactics.disj2_tac,
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
                    have(
                      "!ALL(is_val, (es1 : List[Einstr]))",
                      @meson.asm_meson_tac(ths([@wasm.thm("reduce_ok")])),
                    ),
                    have(
                      "!((es1 : List[Einstr]) == [Trap])",
                      @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_trap")])),
                    ),
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
                        @tactics.undisch_tac(
                          tm(
                            "safe((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{assn}))",
                          ),
                        ),
                        @tactics.struct_cases_tac(
                          @bool.spec(tm("(n : Num)"), @nums.num_cases()),
                        ),
                        @simp.rewrite_tac(ths([safe, sa, safe_trap])),
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
}
