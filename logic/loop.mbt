// The rule for loops: an invariant that holds on entry and at each br 0.
//
// A loop with no parameters steps to a label of arity 0 whose
// continuation is the loop itself, so a br 0 starts it again. The rule's
// proof is by induction on the steps left: the run after a br 0 is a run
// of the loop with fewer steps (safel_down).

///|
fn prove_loop_rule() -> Unit raise {
  let safel = thm("safel")
  // safel for n steps is safel for fewer
  let _ = lemma(
    "safel_down",
    "∀ n : Num, ∀ k : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ l : List[\{assn}], k <= n && safel(n, s, f, es, q, l) → safel(k, s, f, es, q, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        seq([
          @simp.rewrite_tac(ths([@arith.le()])),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
          @simp.rewrite_tac(ths([safel])),
        ]),
        seq([
          @tactics.gen_tac,
          @tactics.struct_cases_tac(@bool.spec(tm("(k : Num)"), @nums.num_cases())),
          @simp.rewrite_tac(ths([safel, @arith.le_suc()])),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.first(@list.List([
            solve(seq([@tactics.disj1_tac, @meson.asm_meson_tac(ths([]))])),
            solve(seq([
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(i : Num)")),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(tm("(lh : Lholed)")),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(@list.List([
                solve(@simp.asm_rewrite_tac(ths([]))),
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                  @meson.asm_meson_tac(ths([])),
                ]),
              ])),
            ])),
            seq([
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([])),
                  seq([
                    @tactics.repeat_tac(@tactics.strip_tac),
                    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                    @meson.asm_meson_tac(ths([])),
                  ]),
                ]),
              ),
            ]),
          ])),
        ]),
      ]),
    ),
  )
  let tb_tf_tbv = thm("tb_tf_tbv")
  let loop_e = "Basic(Loop(Tbv((ot : Option[Valtype])), (bs : List[B_e])))"
  let simple = @bool.gen_all(
    prove_arity(
      "arity_simple_loop",
      "reduce_simple",
      "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [\{loop_e}]), e2) && ALL(is_val, suf) → LENGTH(suf) == 0",
      [thm("no_trap")],
    ),
  )
  let arity = prove_arity(
    "arity_loop",
    "reduce_base",
    "∀ s : Wstore, ∀ f : Wframe, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, APPEND(suf, [\{loop_e}]), s2, f2, e2) && ALL(is_val, suf) → LENGTH(suf) == 0",
    [simple, tb_tf_tbv, @ind_types.injectivity("tf"), @lists.length_map(), @lists.length()],
  )
  let prefix = @bool.gen_all(prove_prefix("loop", [], loop_e, arity))
  let s_ = tm("(s : Wstore)")
  let f_ = tm("(f : Wframe)")
  let cases = @wasm.step_cases(s_, f_, tm("[\{loop_e}]"), compute=false)
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let lists = [@lists.map(), @lists.append(), @lists.append_nil(), @lists.length()]
  let vs0 = "(vs0 : List[Value])"
  let loop_step = lemma(
    "loop_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ ot : Option[Valtype], ∀ bs : List[B_e], reduce(s, f, APPEND(MAP(v_to_e, vs0), [\{loop_e}]), s, f, APPEND(MAP(v_to_e, vs0), [Label(0, [\{loop_e}], MAP(Basic, bs))]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      have(
        "reduce_base((s : Wstore), (f : Wframe), APPEND(MAP(v_to_e, (NIL : List[Value])), [\{loop_e}]), s, f, [Label(0, [\{loop_e}], APPEND(MAP(v_to_e, (NIL : List[Value])), MAP(Basic, (bs : List[B_e]))))])",
        seq([
          @tactics.match_mp_tac(rb[37]),
          @simp.rewrite_tac(ths([tb_tf_tbv, @ind_types.injectivity("tf"), @lists.length()])),
          @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
          @simp.rewrite_tac(ths([@lists.length()])),
          @tactics.try_tac(@meson.meson_tac(ths([]))),
        ]),
      ),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("decomp_reduce"))(th))),
      @tactics.disch_then(th => @tactics.mp_tac(@bool.ispec(tm("LBase(\{vs0}, NIL)"), th))),
      @simp.rewrite_tac(ths([@wasm.thm("lfill")] + lists)),
    ]),
  )
  let sa = "\{sassn}"
  let lb = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => vs == NIL && linv(lc, gs, h)"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => vs == vs0 && linv(lc, gs, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ r : List[Value], vs == APPEND(vs0, r) && qb(r, lc, gs, h))"
  let fr = "(fr : \{hprop})"
  let _ = lemma(
    "sl_loop",
    "∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ linv : (List[Value], List[Value], \{heap}) -> Bool, ∀ qb : \{sa}, ∀ ls : List[\{sa}], ∀ vs0 : List[Value], sl_triple_l(\{lb}, bs, qb, CONS(\{lb}, ls)) → sl_triple_l(\{pre}, [Loop(Tbv(ot), bs)], \{post}, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_l"), thm("triple_l")])),
      @tactics.disch_tac,
      @tactics.x_gen_tac(tm(fr)),
      @tactics.repeat_tac(@tactics.gen_tac),
      // by induction on the steps left, for every state and stack
      @tactics.spec_tac(s_, s_),
      @tactics.spec_tac(f_, f_),
      @tactics.spec_tac(tm("(vs : List[Value])"), tm("(vs : List[Value])")),
      @tactics.spec_tac(tm("(n : Num)"), tm("(n : Num)")),
      @tactics.thenl(
        @nums.induct_tac,
        @list.List([
          @simp.rewrite_tac(ths([safel])),
          seq([
            @tactics.repeat_tac(@tactics.gen_tac),
            @tactics.disch_then(th => @tactics.mp_tac(th)),
            @simp.rewrite_tac(ths(lift_facts())),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths(lists))),
            @simp.rewrite_tac(ths(lists)),
            @simp.rewrite_tac(ths([safel])),
            @tactics.disj2_tac,
            @tactics.disj2_tac,
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                @meson.meson_tac(ths([loop_step])),
                seq([
                  @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                  @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                  @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                  @tactics.disch_tac,
                  @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
                  @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
                  @simp.rewrite_tac(ths([tb_tf_tbv, @ind_types.injectivity("tf")] + lists)),
                  @tactics.repeat_tac(@tactics.strip_tac),
                  subst_vars(),
                  @simp.rewrite_tac(ths(lists)),
                  @tactics.match_mp_tac(thm("label_safe")),
                  @tactics.exists_tac(tm("lift((qb : \{sa}), \{fr})")),
                  @tactics.exists_tac(tm("lift(\{lb}, \{fr})")),
                  @tactics.thenl(
                    @tactics.conj_tac,
                    @list.List([
                      // the body is safe from the invariant
                      seq([
                        @tactics.first_x_assum(th => @tactics.mp_tac(
                          @bool.ispecl(@list.List([tm(fr), s_, f_, tm("(NIL : List[Value])"), tm("(n : Num)")]), th),
                        )),
                        @simp.rewrite_tac(ths(lists + lift_facts())),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          // the body's values leave the loop
                          seq([
                            @tactics.repeat_tac(@tactics.strip_tac),
                            @tactics.match_mp_tac(thm("lift_mono")),
                            @tactics.exists_tac(tm("(qb : \{sa})")),
                            @tactics.exists_tac(tm("(vs : List[Value])")),
                            @simp.asm_rewrite_tac(ths([])),
                            @meson.meson_tac(ths([])),
                          ]),
                          // a br 0 runs the loop again, from the invariant
                          seq([
                            @tactics.repeat_tac(@tactics.gen_tac),
                            @tactics.disch_tac,
                            @tactics.disch_then(th => @tactics.mp_tac(th)),
                            @simp.rewrite_tac(ths(lift_facts())),
                            @tactics.repeat_tac(@tactics.strip_tac),
                            subst_vars(),
                            @simp.rewrite_tac(ths(lists)),
                            @tactics.match_mp_tac(thm("safel_down")),
                            @tactics.exists_tac(tm("(n : Num)")),
                            @simp.asm_rewrite_tac(ths([])),
                            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                            @simp.rewrite_tac(ths(lift_facts())),
                            @meson.asm_meson_tac(ths([])),
                          ]),
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
    ]),
  )
}
