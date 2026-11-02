// Triples with label postconditions, for code that branches.
//
// - safel(n, s, f, es, q, l): as safe, and a run may also stop at a br
//   that leaves es: es is lfill(lh, vs ++ [br (i + depth of lh)]), a br to
//   the i-th label around es, and the i-th assertion of l holds of vs.
// - triple_l and sl_triple_l: as triple and sl_triple, with the label
//   assertions l (innermost first), lifted with the same frame.
//
// safel with no labels is safe, so every rule so far holds with any labels
// (sl_triple_l_of).

///|
fn define_labels() -> Unit raise {
  def(
    "safel",
    "safel(0, (s : Wstore), (f : Wframe), (es : List[Einstr]), (q : \{assn}), (l : List[\{assn}])) == true && safel(SUC(n), s, f, es, q, l) == ((∃ vs : List[Value], es == MAP(v_to_e, vs) && q(s, f, vs)) || (∃ i : Num, ∃ vs : List[Value], ∃ lh : Lholed, i < LENGTH(l) && es == lfill(lh, APPEND(MAP(v_to_e, vs), [Basic(Br(i + lh_depth(lh)))])) && EL(i, l, s, f, vs)) || ((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safel(n, s2, f2, es2, q, l))))",
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
/// For an unfolded `safe`/`safel` step goal: the hypothesis's values case
/// (`values`), then its step case, where every step is safe by `ih`
/// (matched against the goal) with `extra` closing what is left.
fn step_case(ih_exists : String) -> @tactics.Tactic raise {
  seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.exists_tac(tm(ih_exists)),
    @meson.asm_meson_tac(ths([])),
  ])
}

///|
/// `tac`, failing unless it proves the goal.
fn solve(tac : @tactics.Tactic) -> @tactics.Tactic {
  @tactics.then_tac(tac, @tactics.no_tac)
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
  ignore(safe)
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
              subst_vars(),
              @simp.rewrite_tac(ths([safel])),
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(i : Num)")),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(tm("lh_wrap(NIL, (es2 : List[Einstr]), (lh : Lholed))")),
              @simp.asm_rewrite_tac(ths([lfill_wrap, @lists.map(), @lists.append()])),
            ])),
            seq([
              @simp.rewrite_tac(ths([safel])),
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([thm("reduce_app")])),
                  seq([
                    @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                    @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                    @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                    @tactics.disch_tac,
                    have("!ALL(is_val, (es1 : List[Einstr]))", @meson.asm_meson_tac(ths([reduce_ok]))),
                    have("!((es1 : List[Einstr]) == [Trap])", @meson.asm_meson_tac(ths([reduce_not_trap]))),
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
                  ]),
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
  let _ = lemma(
    "sl_br",
    "∀ i : Num, ∀ ls : List[\{sassn}], i < LENGTH(ls) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && EL(i, ls, vb, lc, h)), [Br(i)], (vs : List[Value]) => (lc : List[Value]) => (h : \{heap}) => false, ls)",
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
      @simp.asm_simp_tac(
        ths([
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
        ]),
      ),
      @tactics.exists_tac(tm("(j : Num)")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}
