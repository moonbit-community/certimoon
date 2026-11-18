// Sequencing with returns, block exits, and a specified trap.

///|
fn prove_tlsf_start_sequence() -> Unit raise {
  let a = @logic.assn
  let safer = thm("tlsf_safer_abort")
  let lfill_wrap = @wasm.thm("lfill_wrap")
  let le_suc = arith("∀ m : Num, ∀ n : Num, m <= n → m <= SUC(n)")
  let propagate_trap = seq([
    have(
      "trap_top(APPEND((es1 : List[Einstr]),(es2 : List[Einstr])))",
      startup_meson(ths([thm("abort_trap_append")])),
    ),
    @tactics.mp_tac(
      inst(thm("abort_trap_reduce"), [
        "(s : Wstore)", "(f : Wframe)", "APPEND((es1 : List[Einstr]),(es2 : List[Einstr]))",
        "(t1 : Wstore)", "(t2 : Wframe)", "(t3 : List[Einstr])",
      ]),
    ),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
  ])
  // the steps of APPEND(es1, es2) are steps of es1 (`facts` shows es1 is
  // not values or [Trap])
  let preservation = (facts : @tactics.Tactic) => {
    seq([
      @tactics.x_gen_tac(tm("(t1 : Wstore)")),
      @tactics.x_gen_tac(tm("(t2 : Wframe)")),
      @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
      @tactics.disch_tac,
      facts,
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            [
              "(s : Wstore)", "(f : Wframe)", "(es1 : List[Einstr])", "(es2 : List[Einstr])",
              "(t1 : Wstore)", "(t2 : Wframe)", "(t3 : List[Einstr])",
            ].map(tm),
          ),
          @wasm.thm("reduce_append"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.orelse_tac(
        seq([
          subst_vars(),
          @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
          @tactics.exists_tac(tm("(q : \{a})")),
          startup_meson(ths([le_suc])),
        ]),
        seq([
          have(
            "tlsf_safer_abort((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{a}), (l : List[\{a}]), (rq : \{a}), (ab : (Wstore,Wframe) -> Bool))",
            startup_meson(ths([thm("trap_step")])),
          ),
          @tactics.undisch_tac(
            tm(
              "tlsf_safer_abort((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{a}), (l : List[\{a}]), (rq : \{a}), (ab : (Wstore,Wframe) -> Bool))",
            ),
          ),
          @tactics.struct_cases_tac(
            @bool.spec(tm("(n : Num)"), @nums.num_cases()),
          ),
          @tactics.first(
            @list.List([
              solve(@simp.rewrite_tac(ths([safer]))),
              solve(
                seq([
                  @tactics.disch_then(th => {
                    @tactics.assume_tac(
                      @drule.match_mp(thm("tlsf_safer_abort_trap_assert"))(th),
                    )
                  }),
                  @tactics.match_mp_tac(thm("tlsf_safer_abort_top_trap")),
                  propagate_trap,
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ])
  }
  let es1_facts = (proof : Array[@kernel.Thm]) => {
    seq([
      have("!ALL(is_val, (es1 : List[Einstr]))", startup_meson(ths(proof))),
      have("!((es1 : List[Einstr]) == [Trap])", startup_meson(ths(proof))),
    ])
  }
  let _ = startup_lemma(
    "tlsf_safer_abort_seq",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{a}, ∀ r : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, ∀ ab : (Wstore,Wframe) -> Bool, tlsf_safer_abort(n, s, f, es1, q, l, rq, (ab : (Wstore,Wframe) -> Bool)) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, m <= n → q(s, f, vs) → tlsf_safer_abort(m, s, f, APPEND(MAP(v_to_e, vs), es2), r, l, rq, (ab : (Wstore,Wframe) -> Bool))) → tlsf_safer_abort(n, s, f, APPEND(es1, es2), r, l, rq, (ab : (Wstore,Wframe) -> Bool))",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safer])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.conv_tac(
            @equal.rator_conv(
              @equal.rand_conv(
                @equal.rator_conv(
                  @equal.rand_conv(@simp.pure_once_rewrite_conv(ths([safer]))),
                ),
              ),
            ),
          ),
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              // es1 has ended: es2 runs on its values
              seq([subst_vars(), startup_meson(ths([@arith.le_refl()]))]),
              // es1 stopped at a br: so does APPEND(es1, es2)
              seq([
                @simp.rewrite_tac(ths([safer])),
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(i : Num)")),
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(
                  tm("lh_wrap(NIL, (es2 : List[Einstr]), (lh : Lholed))"),
                ),
                @tactics.repeat_tac(@tactics.conj_tac),
                @tactics.first(
                  @list.List([
                    solve(
                      @simp.asm_rewrite_tac(
                        ths([lfill_wrap, @lists.map(), @lists.append()]),
                      ),
                    ),
                    preservation(
                      es1_facts([thm("br_not_vals"), thm("br_not_trap")]),
                    ),
                  ]),
                ),
              ]),
              // es1 stopped at a return: so does APPEND(es1, es2)
              seq([
                @simp.rewrite_tac(ths([safer])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(
                  tm("lh_wrap(NIL, (es2 : List[Einstr]), (lh : Lholed))"),
                ),
                @simp.asm_rewrite_tac(
                  ths([lfill_wrap, @lists.map(), @lists.append()]),
                ),
              ]),
              // es1 is the specified trap: later instructions cannot run.
              seq([
                subst_vars(),
                @tactics.match_mp_tac(thm("tlsf_safer_abort_top_trap")),
                startup_meson(
                  ths([
                    thm("tlsf_start_literal_trap"),
                    thm("abort_trap_append"),
                    thm("abort_trap_nonvalues"),
                    thm("tlsf_start_br_no_top_trap"),
                    thm("abort_trap_reduce"),
                  ]),
                ),
              ]),
              seq([
                @simp.rewrite_tac(ths([safer])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    startup_meson(ths([thm("reduce_app")])),
                    preservation(
                      es1_facts([
                        @wasm.thm("reduce_ok"),
                        @wasm.thm("reduce_not_trap"),
                      ]),
                    ),
                  ]),
                ),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
}
