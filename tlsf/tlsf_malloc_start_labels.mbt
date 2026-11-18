// A specified initialization abort can escape nested result blocks.

///|
fn prove_tlsf_start_labels() -> Unit raise {
  let a = @logic.assn
  let safer = thm("tlsf_safer_abort")
  let lfill = @wasm.thm("lfill")
  let depth = @wasm.thm("lh_depth")
  let lfilled_eq = @wasm.thm("lfilled_eq")
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let rb_lift = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let einstr_d = @ind_types.distinctness("einstr")
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let vs0 = "(vs0 : List[Value])"
  let label = "Label((m : Num), (e0 : List[Einstr]), (li : List[Einstr]))"
  let base_step = (inner : String, out : String, rule : @tactics.Tactic) => {
    seq([
      @tactics.exists_tac(s),
      @tactics.exists_tac(f),
      @tactics.exists_tac(tm("APPEND(MAP(v_to_e, \{vs0}), \{out})")),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([s, f, tm("LBase(\{vs0}, NIL)"), tm(inner), s, f, tm(out)]),
          @wasm.thm("decomp_reduce"),
        ),
      ),
      @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @tactics.match_mp_tac(rb_lift),
      rule,
    ])
  }
  let steps = (cases : Array[@tactics.Tactic]) => {
    seq([
      @tactics.x_gen_tac(tm("(t1 : Wstore)")),
      @tactics.x_gen_tac(tm("(t2 : Wframe)")),
      @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
      @tactics.disch_tac,
      @tactics.thenl(
        @tactics.first_x_assum(th => {
          @tactics.strip_assume_tac(@drule.match_mp(thm("label_steps"))(th))
        }),
        @list.List(cases),
      ),
    ])
  }
  let le_suc = arith("∀ k : Num, ∀ n : Num, k <= n → k <= SUC(n)")
  let le_n_suc = arith("∀ n : Num, n <= SUC(n)")
  let inside = seq([
    subst_vars(),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.exists_tac(tm("(qb : \{a})")),
    @tactics.exists_tac(tm("(lb : \{a})")),
    startup_meson(ths([le_suc])),
  ])
  let not_vals = seq([
    subst_vars(),
    startup_meson(ths([thm("br_not_vals"), @wasm.thm("all_vals_map")])),
  ])
  let not_trap = seq([subst_vars(), startup_meson(ths([thm("br_not_trap")]))])
  let map_trap = [
    @wasm.thm("map_v_to_e_eq_cons"),
    @wasm.thm("eq_v_to_e"),
    einstr_d,
    @equal.gsym(einstr_d),
  ]
  let arith_suc = arith("∀ i : Num, ∀ d : Num, SUC(i) + d == i + (d + 1)")
  let step3 = seq([
    @tactics.disj2_tac, @tactics.disj2_tac, @tactics.disj2_tac, @tactics.disj2_tac,
  ])
  let _ = startup_lemma(
    "tlsf_safer_abort_label",
    "∀ n : Num, ∀ ab : (Wstore,Wframe) -> Bool, ∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ qb : \{a}, ∀ lb : \{a}, ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, tlsf_safer_abort(n, s, f, li, qb, CONS(lb, l), rq, (ab : (Wstore,Wframe) -> Bool)) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], qb(s, f, vs) → q(s, f, APPEND(vs0, vs))) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ k : Num, k <= n → lb(s, f, vs) → LENGTH(vs) == m && tlsf_safer_abort(k, s, f, APPEND(MAP(v_to_e, vs0), APPEND(MAP(v_to_e, vs), e0)), q, l, rq, (ab : (Wstore,Wframe) -> Bool))) → tlsf_safer_abort(n, s, f, APPEND(MAP(v_to_e, vs0), [\{label}]), q, l, rq, (ab : (Wstore,Wframe) -> Bool))",
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
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            @list.List([
              // the body has ended with values vs: they leave the label
              seq([
                subst_vars(),
                @simp.rewrite_tac(ths([safer])),
                step3,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    base_step(
                      "[Label((m : Num), (e0 : List[Einstr]), MAP(v_to_e, (vs : List[Value])))]",
                      "MAP(v_to_e, (vs : List[Value]))",
                      @tactics.match_accept_tac(rs[27]),
                    ),
                    steps([
                      startup_meson(ths([@wasm.thm("reduce_not_vals")])),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([thm("map_v_to_e_inj")])),
                        ),
                        subst_vars(),
                        @simp.rewrite_tac(
                          ths([@equal.gsym(@lists.map_append())]),
                        ),
                        @tactics.match_mp_tac(thm("tlsf_safer_abort_vals")),
                        startup_meson(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths(map_trap)),
                        ),
                        startup_meson(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([lfilled_eq])),
                        ),
                        startup_meson(
                          ths([thm("br_not_vals"), @wasm.thm("all_vals_map")]),
                        ),
                      ]),
                    ]),
                  ]),
                ),
              ]),
              // the body stopped at a br to label i
              @tactics.thenl(
                @tactics.disj_cases_tac(
                  @bool.spec(tm("(i : Num)"), @nums.num_cases()),
                ),
                @list.List([
                  // to this label: the label takes the br
                  seq([
                    subst_vars(),
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(
                        ths([@lists.el(), @lists.hd(), @arith.add_clauses()]),
                      ),
                    ),
                    @simp.rewrite_tac(ths([safer, @arith.add_clauses()])),
                    step3,
                    have(
                      "LENGTH((vs : List[Value])) == (m : Num)",
                      startup_meson(ths([le_n_suc])),
                    ),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        base_step(
                          "[Label((m : Num), (e0 : List[Einstr]), lfill((lh : Lholed), APPEND(MAP(v_to_e, (vs : List[Value])), [Basic(Br(lh_depth(lh)))])))]",
                          "APPEND(MAP(v_to_e, (vs : List[Value])), (e0 : List[Einstr]))",
                          seq([
                            @tactics.match_mp_tac(rs[29]),
                            @tactics.exists_tac(tm("(lh : Lholed)")),
                            @tactics.exists_tac(tm("lh_depth((lh : Lholed))")),
                            @simp.asm_rewrite_tac(
                              ths([@wasm.thm("lfilled_lfill")]),
                            ),
                          ]),
                        ),
                        steps([
                          inside,
                          not_vals,
                          not_trap,
                          seq([
                            @tactics.rule_assum_tac(
                              @simp.rewrite_rule(ths([lfilled_eq])),
                            ),
                            split_conjs(),
                            subst_vars(),
                            have(
                              "(vs' : List[Value]) == (vs : List[Value])",
                              startup_meson(ths([thm("br_unique")])),
                            ),
                            subst_vars(),
                            startup_meson(ths([le_n_suc])),
                          ]),
                        ]),
                      ]),
                    ),
                  ]),
                  // to a label outside: so does the labelled configuration
                  seq([
                    @tactics.first_x_assum(th => {
                      @tactics.x_choose_tac(tm("(i1 : Num)"), th)
                    }),
                    subst_vars(),
                    @simp.rewrite_tac(ths([safer])),
                    @tactics.disj2_tac,
                    @tactics.disj1_tac,
                    @tactics.exists_tac(tm("(i1 : Num)")),
                    @tactics.exists_tac(tm("(vs : List[Value])")),
                    @tactics.exists_tac(
                      tm(
                        "LRec(\{vs0}, (m : Num), (e0 : List[Einstr]), (lh : Lholed), NIL)",
                      ),
                    ),
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(
                        ths([
                          @lists.el(),
                          @lists.tl(),
                          @lists.length(),
                          @arith.lt_suc(),
                        ]),
                      ),
                    ),
                    @tactics.repeat_tac(@tactics.conj_tac),
                    @tactics.first(
                      @list.List([
                        solve(
                          @simp.asm_rewrite_tac(ths([lfill, depth, arith_suc])),
                        ),
                        steps([
                          inside,
                          not_vals,
                          not_trap,
                          seq([
                            @tactics.rule_assum_tac(
                              @simp.rewrite_rule(ths([lfilled_eq])),
                            ),
                            split_conjs(),
                            subst_vars(),
                            seq([
                              have(
                                "F",
                                seq([
                                  @tactics.first_assum(th => {
                                    @tactics.strip_assume_tac(
                                      @drule.match_mp(thm("br_unique"))(th),
                                    )
                                  }),
                                  @int.asm_arith_tac,
                                ]),
                              ),
                              @tactics.first_assum(th => @tactics.contr_tac(th)),
                            ]),
                          ]),
                        ]),
                      ]),
                    ),
                  ]),
                ]),
              ),
              // the body stopped at a return: so does the labelled configuration
              seq([
                subst_vars(),
                @simp.rewrite_tac(ths([safer])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(
                  tm(
                    "LRec(\{vs0}, (m : Num), (e0 : List[Einstr]), (lh : Lholed), NIL)",
                  ),
                ),
                @simp.asm_rewrite_tac(ths([lfill, @lists.append_nil()])),
              ]),
              // A trap in the body propagates without executing the continuation.
              seq([
                subst_vars(),
                @simp.rewrite_tac(ths([safer])),
                step3,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    base_step(
                      "[Label((m : Num),(e0 : List[Einstr]),[Trap])]",
                      "[Trap]",
                      @tactics.match_accept_tac(rs[28]),
                    ),
                    steps([
                      startup_meson(ths([@wasm.thm("reduce_not_trap")])),
                      startup_meson(ths([thm("vals_not_trap")])),
                      seq([
                        subst_vars(),
                        @tactics.match_mp_tac(thm("tlsf_safer_abort_top_trap")),
                        startup_meson(
                          ths([
                            thm("abort_trap_drop_values"),
                            thm("tlsf_start_literal_trap"),
                          ]),
                        ),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([lfilled_eq])),
                        ),
                        split_conjs(),
                        subst_vars(),
                        startup_meson(ths([thm("br_not_trap")])),
                      ]),
                    ]),
                  ]),
                ),
              ]),
              // the body steps
              seq([
                @simp.rewrite_tac(ths([safer])),
                step3,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    startup_meson(ths([thm("reduce_label")])),
                    steps([
                      inside,
                      seq([
                        subst_vars(),
                        startup_meson(ths([@wasm.thm("reduce_not_vals")])),
                      ]),
                      seq([
                        subst_vars(),
                        startup_meson(ths([@wasm.thm("reduce_not_trap")])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([lfilled_eq])),
                        ),
                        subst_vars(),
                        startup_meson(ths([thm("br_stuck"), @arith.le_refl()])),
                      ]),
                    ]),
                  ]),
                ),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_label_top",
    "∀ n : Num, ∀ ab : (Wstore,Wframe) -> Bool, ∀ s : Wstore, ∀ f : Wframe, ∀ m : Num, ∀ li : List[Einstr], ∀ qb : \{a}, ∀ rb : \{a}, tlsf_safer_abort(n, s, f, li, qb, [qb], rb, (ab : (Wstore,Wframe) -> Bool)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qb(s2, f2, vs) → LENGTH(vs) == m) → tlsf_safer_abort(n, s, f, [Label(m, NIL, li)], qb, NIL, rb, (ab : (Wstore,Wframe) -> Bool))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            [
              "(n : Num)",
              "(ab : (Wstore,Wframe) -> Bool)",
              "(s : Wstore)",
              "(f : Wframe)",
              "(NIL : List[Value])",
              "(m : Num)",
              "(NIL : List[Einstr])",
              "(li : List[Einstr])",
              "(qb : \{a})",
              "(qb : \{a})",
              "(qb : \{a})",
              "(NIL : List[\{a}])",
              "(rb : \{a})",
            ].map(tm),
          ),
          thm("tlsf_safer_abort_label"),
        ),
      ),
      @simp.rewrite_tac(
        ths([@lists.map(), @lists.append(), @lists.append_nil()]),
      ),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first(
        @list.List([
          solve(startup_meson(ths([]))),
          solve(
            seq([
              @tactics.match_mp_tac(thm("tlsf_safer_abort_vals")),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
