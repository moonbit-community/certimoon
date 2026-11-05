// Triples with label postconditions, for code that branches.
//
// - safel(n, s, f, es, q, l): as safe, and a run may also stop at a br
//   that leaves es: es is lfill(lh, vs ++ [br (i + depth of lh)]), a br to
//   the i-th label around es, the i-th assertion of l holds of vs, and
//   (such an es does not step, but this is easier to keep than to prove)
//   every step is safe.
// - triple_l and sl_triple_l: as triple and sl_triple, with the label
//   assertions l (innermost first), lifted with the same frame.
//
// safel with no labels is safe, so every rule so far holds with any labels
// (sl_triple_l_of). Consequence (sl_conseq_l) also weakens each label
// assertion, and the frame rule (sl_frame_l) frames the labels too.

///|
fn define_labels() -> Unit raise {
  def(
    "safel",
    "safel(0, (s : Wstore), (f : Wframe), (es : List[Einstr]), (q : \{assn}), (l : List[\{assn}])) == true && safel(SUC(n), s, f, es, q, l) == ((∃ vs : List[Value], es == MAP(v_to_e, vs) && q(s, f, vs)) || (∃ i : Num, ∃ vs : List[Value], ∃ lh : Lholed, i < LENGTH(l) && es == lfill(lh, APPEND(MAP(v_to_e, vs), [Basic(Br(i + lh_depth(lh)))])) && EL(i, l, s, f, vs) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safel(n, s2, f2, es2, q, l))) || ((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safel(n, s2, f2, es2, q, l))))",
  )
  def(
    "triple_l",
    "triple_l((p : \{assn}), (bs : List[B_e]), (q : \{assn}), (l : List[\{assn}])) == (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ n : Num, p(s, f, vs) → safel(n, s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs)), q, l))",
  )
  def(
    "sl_triple_l",
    "sl_triple_l((p : \{sassn}), (bs : List[B_e]), (q : \{sassn}), (ls : List[\{sassn}])) == (∀ r : \{hprop}, triple_l(lift(p, r), bs, lift(q, r), MAP((x : \{sassn}) => lift(x, r), ls)))",
  )
}

///|
fn prove_labels() -> Unit raise {
  let safe = thm("safe")
  let safel = thm("safel")
  let safe_safel = lemma(
    "safe_safel",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ l : List[\{assn}], safe(n, s, f, es, q) → safel(n, s, f, es, q, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @simp.rewrite_tac(ths([safe, safel])),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.orelse_tac(
            seq([
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @meson.asm_meson_tac(ths([])),
            ]),
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
          ),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "sl_triple_l_of",
    "∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ ls : List[\{sassn}], sl_triple(p, bs, q) → sl_triple_l(p, bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("sl_triple_l"), thm("triple"), thm("triple_l")])),
      @meson.meson_tac(ths([safe_safel])),
    ]),
  )
  let reduce_ok = @wasm.thm("reduce_ok")
  let reduce_not_trap = @wasm.thm("reduce_not_trap")
  let einstr = @ind_types.distinctness("einstr")
  let safel_trap = lemma(
    "safel_trap",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, ∀ l : List[\{assn}], !safel(SUC(n), s, f, [Trap], q, l)",
    seq([
      @simp.rewrite_tac(
        ths([safel, reduce_not_trap, @wasm.thm("map_v_to_e_cons"), @wasm.thm("eq_v_to_e"), einstr, @equal.gsym(einstr)]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("lfill_trap"))(@equal.gsym(th)))),
      @simp.rewrite_tac(
        ths([thm("snoc_eq"), @lists.append_eq_nil(), @lists.not_cons_nil(), @lists.last(), einstr, @equal.gsym(einstr)]),
      ),
    ]),
  )
  let lfill_wrap = @wasm.thm("lfill_wrap")
  let br_code = "lfill((lh : Lholed), APPEND(MAP(v_to_e, (vs : List[Value])), [Basic(Br((k : Num)))]))"
  let not_cons = [@lists.not_cons_nil(), @equal.gsym(@lists.not_cons_nil())]
  let br_not_vals = lemma(
    "br_not_vals",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ k : Num, !ALL(is_val, \{br_code})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("lfill_vals"))(th))),
      @simp.rewrite_tac(ths([@lists.all_append(), @lists.all(), @wasm.thm("is_val_clauses"), @wasm.thm("is_val_basic"), @ind_types.distinctness("b_e")])),
    ]),
  )
  let br_not_trap = lemma(
    "br_not_trap",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ k : Num, !(\{br_code} == [Trap])",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("lfill_trap"))(th))),
      @simp.rewrite_tac(ths([thm("snoc_eq"), @lists.append_eq_nil(), @lists.last(), einstr, @equal.gsym(einstr)] + not_cons)),
    ]),
  )
  // the steps of APPEND(es1, es2) are safe when es1's are, and es1 is not
  // values or [Trap] (`facts` shows that)
  let preservation = (facts : @tactics.Tactic) => seq([
    @tactics.x_gen_tac(tm("(t1 : Wstore)")),
    @tactics.x_gen_tac(tm("(t2 : Wframe)")),
    @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
    @tactics.disch_tac,
    facts,
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
      seq([
        subst_vars(),
        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
        @tactics.exists_tac(tm("(q : \{assn})")),
        @meson.asm_meson_tac(ths([])),
      ]),
      seq([
        have(
          "safel((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{assn}), (l : List[\{assn}]))",
          @meson.asm_meson_tac(ths([thm("trap_step")])),
        ),
        @tactics.undisch_tac(tm("safel((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{assn}), (l : List[\{assn}]))")),
        @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
        @simp.rewrite_tac(ths([safel, safel_trap])),
      ]),
    ),
  ])
  let es1_facts = (proof : Array[@kernel.Thm]) => seq([
    have("!ALL(is_val, (es1 : List[Einstr]))", @meson.asm_meson_tac(ths(proof))),
    have("!((es1 : List[Einstr]) == [Trap])", @meson.asm_meson_tac(ths(proof))),
  ])
  let safel_seq = lemma(
    "safel_seq",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{assn}, ∀ r : \{assn}, ∀ l : List[\{assn}], safel(n, s, f, es1, q, l) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, q(s, f, vs) → safel(m, s, f, APPEND(MAP(v_to_e, vs), es2), r, l)) → safel(n, s, f, APPEND(es1, es2), r, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.conv_tac(
            @equal.rator_conv(@equal.rand_conv(@equal.rator_conv(@equal.rand_conv(@simp.pure_once_rewrite_conv(ths([safel])))))),
          ),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.first(@list.List([
            // es1 has ended: es2 runs on its values
            solve(seq([subst_vars(), @meson.asm_meson_tac(ths([]))])),
            // es1 stopped at a br: so does APPEND(es1, es2)
            solve(seq([
              @simp.rewrite_tac(ths([safel])),
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(i : Num)")),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(tm("lh_wrap(NIL, (es2 : List[Einstr]), (lh : Lholed))")),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(@list.List([
                solve(@simp.asm_rewrite_tac(ths([lfill_wrap, @lists.map(), @lists.append()]))),
                preservation(es1_facts([br_not_vals, br_not_trap])),
              ])),
            ])),
            seq([
              @simp.rewrite_tac(ths([safel])),
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([thm("reduce_app")])),
                  preservation(es1_facts([reduce_ok, reduce_not_trap])),
                ]),
              ),
            ]),
          ])),
        ]),
      ]),
    ),
  )
  let triple_l = thm("triple_l")
  let triple_l_seq = lemma(
    "triple_l_seq",
    "∀ p : \{assn}, ∀ bs1 : List[B_e], ∀ q : \{assn}, ∀ bs2 : List[B_e], ∀ r : \{assn}, ∀ l : List[\{assn}], triple_l(p, bs1, q, l) && triple_l(q, bs2, r, l) → triple_l(p, APPEND(bs1, bs2), r, l)",
    seq([
      @simp.rewrite_tac(ths([triple_l, @lists.map_append(), @lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(safel_seq),
      @tactics.exists_tac(tm("(q : \{assn})")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_seq_l",
    "∀ p : \{sassn}, ∀ bs1 : List[B_e], ∀ q : \{sassn}, ∀ bs2 : List[B_e], ∀ r : \{sassn}, ∀ ls : List[\{sassn}], sl_triple_l(p, bs1, q, ls) && sl_triple_l(q, bs2, r, ls) → sl_triple_l(p, APPEND(bs1, bs2), r, ls)",
    seq([@simp.rewrite_tac(ths([thm("sl_triple_l")])), @meson.meson_tac(ths([triple_l_seq]))]),
  )
  prove_label_structural()
  // a br after values does not step
  let nobr_simple = @bool.gen_all(
    prove_arity(
      "nobr_simple",
      "reduce_simple",
      "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [Basic(Br((k : Num)))]), e2) && ALL(is_val, suf) → false",
      [thm("no_trap")],
    ),
  )
  let nobr = @bool.gen_all(
    prove_arity(
      "nobr_base",
      "reduce_base",
      "∀ s : Wstore, ∀ f : Wframe, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, APPEND(suf, [Basic(Br((k : Num)))]), s2, f2, e2) && ALL(is_val, suf) → false",
      [nobr_simple],
    ),
  )
  let br_no_step = lemma(
    "br_no_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ cs : List[Einstr], ∀ k : Num, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], ALL(is_val, cs) → !reduce(s, f, APPEND(cs, [Basic(Br(k))]), s2, f2, es2)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(s : Wstore)"),
            tm("(f : Wframe)"),
            tm("(cs : List[Einstr])"),
            tm("Basic(Br((k : Num)))"),
            tm("(s2 : Wstore)"),
            tm("(f2 : Wframe)"),
            tm("(es2 : List[Einstr])"),
          ]),
          @wasm.thm("step_basic"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([einstr])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.all_append()]))),
      @meson.asm_meson_tac(ths([nobr])),
    ]),
  )
  let simp_br = [
    @wasm.thm("lfill"),
    @wasm.thm("lh_depth"),
    @lists.map_append(),
    @lists.map(),
    @equal.gsym(@lists.append_assoc()),
    @lists.append(),
    @lists.append_nil(),
    @arith.add_clauses(),
    @lists.length_map(),
    @lists.el_map(),
    thm("lift"),
  ]
  let _ = lemma(
    "sl_br",
    "∀ i : Num, ∀ ls : List[\{sassn}], i < LENGTH(ls) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && EL(i, ls, vb, lc, gs, ms, h)), [Br(i)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => false, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([thm("sl_triple_l"), triple_l])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([safel])),
      @tactics.disj2_tac,
      @tactics.disj1_tac,
      @tactics.exists_tac(tm("(i : Num)")),
      @tactics.exists_tac(tm("(vb : List[Value])")),
      @tactics.exists_tac(tm("LBase((vs0 : List[Value]), NIL)")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([
        // the br does not step
        solve(seq([
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.first_x_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([@lists.map_append(), @lists.map()])),
          @simp.simp_tac(ths([br_no_step, @lists.all_append(), @wasm.thm("all_vals_map")])),
        ])),
        solve(seq([@simp.asm_simp_tac(ths(simp_br)), @tactics.exists_tac(tm("(j : Num)")), @simp.asm_rewrite_tac(ths([]))])),
        solve(@simp.asm_simp_tac(ths(simp_br))),
      ])),
    ]),
  )
}

///|
/// The structural rules with labels: consequence, which weakens the
/// postcondition and each label assertion, and the frame rule, which frames
/// the labels too.
fn prove_label_structural() -> Unit raise {
  let safel = thm("safel")
  let triple_l = thm("triple_l")
  let sl_triple_l = thm("sl_triple_l")
  let lift_mono = thm("lift_mono")
  // l2 is pointwise weaker than l
  let weaker = (l : String, l2 : String) => "LENGTH(\{l2}) == LENGTH(\{l}) && (∀ i : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], i < LENGTH(\{l}) && EL(i, \{l}, s, f, vs) → EL(i, \{l2}, s, f, vs))"
  let safel_mono = lemma(
    "safel_mono",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ q2 : \{assn}, ∀ l : List[\{assn}], ∀ l2 : List[\{assn}], (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) && \{weaker("l", "l2")} && safel(n, s, f, es, q, l) → safel(n, s, f, es, q2, l2)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @simp.rewrite_tac(ths([safel])),
          // ended in values, stopped at a br, or steps
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              seq([
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @meson.asm_meson_tac(ths([])),
              ]),
              seq([
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(i : Num)")),
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(tm("(lh : Lholed)")),
                @tactics.thenl(
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @list.List([
                    @simp.asm_rewrite_tac(ths([])),
                    @simp.asm_rewrite_tac(ths([])),
                    seq([
                      @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                      @simp.asm_rewrite_tac(ths([])),
                    ]),
                    seq([
                      @tactics.repeat_tac(@tactics.strip_tac),
                      @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                      @tactics.exists_tac(tm("(q : \{assn})")),
                      @tactics.exists_tac(tm("(l : List[\{assn}])")),
                      @meson.asm_meson_tac(ths([])),
                    ]),
                  ]),
                ),
              ]),
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
                      @tactics.exists_tac(tm("(q : \{assn})")),
                      @tactics.exists_tac(tm("(l : List[\{assn}])")),
                      @meson.asm_meson_tac(ths([])),
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
  let triple_l_conseq = lemma(
    "triple_l_conseq",
    "∀ p : \{assn}, ∀ p2 : \{assn}, ∀ bs : List[B_e], ∀ q : \{assn}, ∀ q2 : \{assn}, ∀ l : List[\{assn}], ∀ l2 : List[\{assn}], (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], p2(s, f, vs) → p(s, f, vs)) && triple_l(p, bs, q, l) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) && \{weaker("l", "l2")} → triple_l(p2, bs, q2, l2)",
    seq([
      @simp.rewrite_tac(ths([triple_l])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(safel_mono),
      @tactics.exists_tac(tm("(q : \{assn})")),
      @tactics.exists_tac(tm("(l : List[\{assn}])")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let lift_l = "MAP((x : \{sassn}) => lift(x, (r : \{hprop})), (ls : List[\{sassn}]))"
  let _ = lemma(
    "sl_conseq_l",
    "∀ p : \{sassn}, ∀ p2 : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ q2 : \{sassn}, ∀ ls : List[\{sassn}], ∀ ls2 : List[\{sassn}], (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, p2(vs, lc, gs, ms, h) → p(vs, lc, gs, ms, h)) && sl_triple_l(p, bs, q, ls) && (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, q(vs, lc, gs, ms, h) → q2(vs, lc, gs, ms, h)) && LENGTH(ls2) == LENGTH(ls) && (∀ i : Num, ∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, i < LENGTH(ls) && EL(i, ls, vs, lc, gs, ms, h) → EL(i, ls2, vs, lc, gs, ms, h)) → sl_triple_l(p2, bs, q2, ls2)",
    seq([
      @simp.rewrite_tac(ths([sl_triple_l])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(triple_l_conseq),
      @tactics.exists_tac(tm("lift((p : \{sassn}), (r : \{hprop}))")),
      @tactics.exists_tac(tm("lift((q : \{sassn}), (r : \{hprop}))")),
      @tactics.exists_tac(tm(lift_l)),
      // the triple and the lengths
      @simp.asm_rewrite_tac(ths([@lists.length_map()])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([
        // the pre- and postcondition
        solve(seq([
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.match_mp_tac(lift_mono),
          @meson.asm_meson_tac(ths([])),
        ])),
        // each label
        solve(seq([
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.first_x_assum(th => @tactics.mp_tac(th)),
          have("(i : Num) < LENGTH((ls2 : List[\{sassn}]))", @simp.asm_rewrite_tac(ths([]))),
          @simp.asm_simp_tac(ths([@lists.el_map()])),
          @tactics.disch_tac,
          @tactics.match_mp_tac(lift_mono),
          @tactics.exists_tac(tm("EL((i : Num), (ls : List[\{sassn}]))")),
          @tactics.exists_tac(tm("(vs : List[Value])")),
          @meson.asm_meson_tac(ths([])),
        ])),
      ])),
    ]),
  )
  let _ = lemma(
    "sl_frame_l",
    "∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ ls : List[\{sassn}], ∀ fr : \{hprop}, sl_triple_l(p, bs, q, ls) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => star(p(vs, lc, gs, ms), fr), bs, (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => star(q(vs, lc, gs, ms), fr), MAP((x : \{sassn}) => (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => star(x(vs, lc, gs, ms), fr), ls))",
    seq([
      @simp.rewrite_tac(ths([sl_triple_l, @equal.gsym(@lists.map_o()), @trivia.o_def(), thm("lift_frame")])),
      @meson.meson_tac(ths([])),
    ]),
  )
}

///|
/// More structural rules: an ∃ or a pure condition comes out of a
/// precondition (sl_ex_l, sl_pure_l), the empty program (sl_nil_l), and
/// a triple with no labels is a triple (sl_triple_of_l).
fn prove_label_extras() -> Unit raise {
  let safe = thm("safe")
  let safel = thm("safel")
  let sl_triple_l = thm("sl_triple_l")
  let triple_l = thm("triple_l")
  let lift = thm("lift")
  let pp = "(pp : (A, List[Value], List[Value], List[Value], Num, \{heap}) -> Bool)"
  let lift_ex = lemma(
    "lift_ex",
    "∀ pp : (A, List[Value], List[Value], List[Value], Num, \{heap}) -> Bool, ∀ r : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], lift((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ x : A, \{pp}(x, vs, lc, gs, ms, h)), r, s, f, vs) == (∃ x : A, lift(pp(x), r, s, f, vs))",
    seq([
      @simp.rewrite_tac(ths([lift, thm("star_ex"), @class.eta_ax()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let lift_pure = lemma(
    "lift_pure",
    "∀ c : Bool, ∀ p : \{sassn}, ∀ r : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], lift((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => c && p(vs, lc, gs, ms, h), r, s, f, vs) == (c && lift(p, r, s, f, vs))",
    seq([
      @simp.rewrite_tac(ths([lift, thm("star_pure"), @class.eta_ax()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_ex_l",
    "∀ pp : (A, List[Value], List[Value], List[Value], Num, \{heap}) -> Bool, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ ls : List[\{sassn}], (∀ x : A, sl_triple_l(pp(x), bs, q, ls)) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ x : A, pp(x, vs, lc, gs, ms, h)), bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([sl_triple_l, triple_l, lift_ex])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_pure_l",
    "∀ c : Bool, ∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ ls : List[\{sassn}], (c → sl_triple_l(p, bs, q, ls)) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => c && p(vs, lc, gs, ms, h), bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([sl_triple_l, triple_l, lift_pure])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_nil_l",
    "∀ p : \{sassn}, ∀ ls : List[\{sassn}], sl_triple_l(p, NIL, p, ls)",
    seq([
      @simp.rewrite_tac(ths([sl_triple_l, triple_l, @lists.map(), @lists.append_nil()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safel_vals")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let safel_nil = lemma(
    "safel_nil",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, safel(n, s, f, es, q, NIL) → safe(n, s, f, es, q)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safe])),
        seq([
          @simp.rewrite_tac(ths([safel, safe, @lists.length(), arith("∀ n : Num, !(n < 0)")])),
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              seq([
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @meson.asm_meson_tac(ths([])),
              ]),
              seq([
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
            ]),
          ),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "sl_triple_of_l",
    "∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, sl_triple_l(p, bs, q, NIL) → sl_triple(p, bs, q)",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple"), sl_triple_l, thm("triple"), triple_l, @lists.map()])),
      @meson.meson_tac(ths([safel_nil])),
    ]),
  )
}
