// Safety with returns.
//
// - safer(n, s, f, es, q, l, rq): as safel, and a run may also stop at a
//   return: es is lfill(lh, vs ++ [return]) and rq holds of vs. A return
//   does not step outside its frame (return_stuck), so this case needs no
//   steps after it.
//
// safel is safer with a return assertion that never holds (safel_safer,
// safer_safel). The lemmas here are safel's (sequencing, labels, frames),
// with returns: sequencing and labels pass a return on to the code around
// them, and a frame takes it, with the return's values as its results.
// safer_seq's continuation is asked to be safe for at most the steps left,
// so that a triple may be proved for a number of steps only (specs.mbt).

///|
fn define_safer() -> Unit raise {
  let a = assn
  def(
    "safer",
    "safer(0, (s : Wstore), (f : Wframe), (es : List[Einstr]), (q : \{a}), (l : List[\{a}]), (rq : \{a})) == true && safer(SUC(n), s, f, es, q, l, rq) == ((∃ vs : List[Value], es == MAP(v_to_e, vs) && q(s, f, vs)) || (∃ i : Num, ∃ vs : List[Value], ∃ lh : Lholed, i < LENGTH(l) && es == lfill(lh, APPEND(MAP(v_to_e, vs), [Basic(Br(i + lh_depth(lh)))])) && EL(i, l, s, f, vs) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safer(n, s2, f2, es2, q, l, rq))) || (∃ vs : List[Value], ∃ lh : Lholed, es == lfill(lh, APPEND(MAP(v_to_e, vs), [Basic(Return)])) && rq(s, f, vs)) || ((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safer(n, s2, f2, es2, q, l, rq))))",
  )
}

///|
/// The steps clause of safer(SUC(n), ...): a step exists (`exists`), and
/// every step is safe (`each`, after the step's variables and hypothesis).
fn safer_steps(
  exists : @tactics.Tactic,
  each : @tactics.Tactic,
) -> @tactics.Tactic {
  seq([
    @tactics.disj2_tac,
    @tactics.disj2_tac,
    @tactics.disj2_tac,
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([exists, seq([@tactics.repeat_tac(@tactics.strip_tac), each])]),
    ),
  ])
}

///|
fn prove_safer_basics() -> Unit raise {
  let a = assn
  let safer = thm("safer")
  let safel = thm("safel")
  let n_cases = (v : String) => {
    @tactics.struct_cases_tac(@bool.spec(tm("(\{v} : Num)"), @nums.num_cases()))
  }
  let _ = lemma(
    "safer_vals",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, q(s, f, vs) → safer(n, s, f, MAP(v_to_e, vs), q, l, rq)",
    seq([
      @tactics.gen_tac,
      n_cases("n"),
      @simp.rewrite_tac(ths([safer])),
      @meson.meson_tac(ths([])),
    ]),
  )
  // the step clause, by the induction hypothesis
  let by_ih = seq([
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @meson.asm_meson_tac(ths([])),
  ])
  let br_case = (rest : @tactics.Tactic) => {
    seq([
      @tactics.disj2_tac,
      @tactics.disj1_tac,
      @tactics.exists_tac(tm("(i : Num)")),
      @tactics.exists_tac(tm("(vs : List[Value])")),
      @tactics.exists_tac(tm("(lh : Lholed)")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@simp.asm_rewrite_tac(ths([]))),
          solve(
            seq([
              @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          seq([@tactics.repeat_tac(@tactics.strip_tac), rest]),
        ]),
      ),
    ])
  }
  let _ = lemma(
    "safel_safer",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, safel(n, s, f, es, q, l) → safer(n, s, f, es, q, l, rq)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safer])),
        seq([
          @simp.rewrite_tac(ths([safel, safer])),
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              seq([
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @simp.asm_rewrite_tac(ths([])),
              ]),
              br_case(by_ih),
              safer_steps(@meson.asm_meson_tac(ths([])), by_ih),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "safer_safel",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], !rq(s, f, vs)) && safer(n, s, f, es, q, l, rq) → safel(n, s, f, es, q, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @simp.rewrite_tac(ths([safel, safer])),
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              seq([
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @simp.asm_rewrite_tac(ths([])),
              ]),
              br_case(
                seq([
                  @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                  @tactics.exists_tac(tm("(rq : \{a})")),
                  @meson.asm_meson_tac(ths([])),
                ]),
              ),
              @meson.asm_meson_tac(ths([])),
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
                      @tactics.exists_tac(tm("(rq : \{a})")),
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
  let weaker = (l : String, l2 : String) => {
    "LENGTH(\{l2}) == LENGTH(\{l}) && (∀ i : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], i < LENGTH(\{l}) && EL(i, \{l}, s, f, vs) → EL(i, \{l2}, s, f, vs))"
  }
  let mono_ih = seq([
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.exists_tac(tm("(q : \{a})")),
    @tactics.exists_tac(tm("(l : List[\{a}])")),
    @tactics.exists_tac(tm("(rq : \{a})")),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "safer_mono",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ q2 : \{a}, ∀ l : List[\{a}], ∀ l2 : List[\{a}], ∀ rq : \{a}, ∀ rq2 : \{a}, (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) && \{weaker("l", "l2")} && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], rq(s, f, vs) → rq2(s, f, vs)) && safer(n, s, f, es, q, l, rq) → safer(n, s, f, es, q2, l2, rq2)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safer])),
        seq([
          @simp.rewrite_tac(ths([safer])),
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
                    seq([@tactics.repeat_tac(@tactics.strip_tac), mono_ih]),
                  ]),
                ),
              ]),
              seq([
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(tm("(lh : Lholed)")),
                @meson.asm_meson_tac(ths([])),
              ]),
              safer_steps(@meson.asm_meson_tac(ths([])), mono_ih),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "safer_down",
    "∀ n : Num, ∀ k : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, k <= n && safer(n, s, f, es, q, l, rq) → safer(k, s, f, es, q, l, rq)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        seq([
          @simp.rewrite_tac(ths([@arith.le()])),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
          @simp.rewrite_tac(ths([safer])),
        ]),
        seq([
          @tactics.gen_tac,
          n_cases("k"),
          @simp.rewrite_tac(ths([safer, @arith.le_suc()])),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.first(
            @list.List([
              solve(seq([@tactics.disj1_tac, @meson.asm_meson_tac(ths([]))])),
              solve(
                seq([
                  @tactics.disj2_tac,
                  @tactics.disj1_tac,
                  @tactics.exists_tac(tm("(i : Num)")),
                  @tactics.exists_tac(tm("(vs : List[Value])")),
                  @tactics.exists_tac(tm("(lh : Lholed)")),
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @tactics.first(
                    @list.List([
                      solve(@simp.asm_rewrite_tac(ths([]))),
                      seq([
                        @tactics.repeat_tac(@tactics.strip_tac),
                        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                    ]),
                  ),
                ]),
              ),
              solve(
                seq([
                  @tactics.disj2_tac,
                  @tactics.disj2_tac,
                  @tactics.disj1_tac,
                  @meson.asm_meson_tac(ths([])),
                ]),
              ),
              safer_steps(
                @meson.asm_meson_tac(ths([])),
                seq([
                  @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                  @meson.asm_meson_tac(ths([])),
                ]),
              ),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let einstr = @ind_types.distinctness("einstr")
  let _ = lemma(
    "safer_trap",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, !safer(SUC(n), s, f, [Trap], q, l, rq)",
    seq([
      @simp.rewrite_tac(
        ths([
          safer,
          @wasm.thm("reduce_not_trap"),
          @wasm.thm("map_v_to_e_cons"),
          @wasm.thm("eq_v_to_e"),
          einstr,
          @equal.gsym(einstr),
        ]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => {
        @tactics.mp_tac(
          @drule.match_mp(@wasm.thm("lfill_trap"))(@equal.gsym(th)),
        )
      }),
      @simp.rewrite_tac(
        ths([
          thm("snoc_eq"),
          @lists.append_eq_nil(),
          @lists.not_cons_nil(),
          @lists.last(),
          einstr,
          @equal.gsym(einstr),
        ]),
      ),
    ]),
  )
  // one step, to es2, and only to es2
  let _ = lemma(
    "safer_det_step",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ es1 : List[Einstr], ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, reduce(s, f, es, s, f, es1) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → s2 == s && f2 == f && es2 == es1) && safer(n, s, f, es1, q, l, rq) → safer(SUC(n), s, f, es, q, l, rq)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.rewrite_tac(ths([safer])),
      safer_steps(
        @meson.asm_meson_tac(ths([])),
        seq([
          @tactics.first_x_assum(th => {
            @tactics.first_assum(r => @tactics.mp_tac(@drule.match_mp(th)(r)))
          }),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          subst_vars(),
          @tactics.first_assum(th => @tactics.accept_tac(th)),
        ]),
      ),
    ]),
  )
}

///|
/// Sequencing with returns, the continuation safe for the steps left.
fn prove_safer_seq() -> Unit raise {
  let a = assn
  let safer = thm("safer")
  let lfill_wrap = @wasm.thm("lfill_wrap")
  let le_suc = arith("∀ m : Num, ∀ n : Num, m <= n → m <= SUC(n)")
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
          @meson.asm_meson_tac(ths([le_suc])),
        ]),
        seq([
          have(
            "safer((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{a}), (l : List[\{a}]), (rq : \{a}))",
            @meson.asm_meson_tac(ths([thm("trap_step")])),
          ),
          @tactics.undisch_tac(
            tm(
              "safer((n : Num), (s : Wstore), (f : Wframe), [Trap], (q : \{a}), (l : List[\{a}]), (rq : \{a}))",
            ),
          ),
          @tactics.struct_cases_tac(
            @bool.spec(tm("(n : Num)"), @nums.num_cases()),
          ),
          @simp.rewrite_tac(ths([safer, thm("safer_trap")])),
        ]),
      ),
    ])
  }
  let es1_facts = (proof : Array[@kernel.Thm]) => {
    seq([
      have(
        "!ALL(is_val, (es1 : List[Einstr]))",
        @meson.asm_meson_tac(ths(proof)),
      ),
      have(
        "!((es1 : List[Einstr]) == [Trap])",
        @meson.asm_meson_tac(ths(proof)),
      ),
    ])
  }
  let _ = lemma(
    "safer_seq",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{a}, ∀ r : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, safer(n, s, f, es1, q, l, rq) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, m <= n → q(s, f, vs) → safer(m, s, f, APPEND(MAP(v_to_e, vs), es2), r, l, rq)) → safer(n, s, f, APPEND(es1, es2), r, l, rq)",
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
              seq([subst_vars(), @meson.asm_meson_tac(ths([@arith.le_refl()]))]),
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
              seq([
                @simp.rewrite_tac(ths([safer])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    @meson.asm_meson_tac(ths([thm("reduce_app")])),
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

///|
/// Returns: where a return is, and that a frame takes one.
fn prove_ret_facts() -> Unit raise {
  let lfill = @wasm.thm("lfill")
  let depth = @wasm.thm("lh_depth")
  let is_val = [@wasm.thm("is_val_clauses"), @wasm.thm("is_val_basic")]
  let einstr_d = @ind_types.distinctness("einstr")
  let b_e_d = @ind_types.distinctness("b_e")
  let ctor = [
    einstr_d,
    @equal.gsym(einstr_d),
    @ind_types.injectivity("einstr"),
    b_e_d,
    @equal.gsym(b_e_d),
    @ind_types.injectivity("b_e"),
  ]
  let normal = [
    lfill,
    depth,
    @equal.gsym(@lists.append_assoc()),
    @lists.append(),
    @wasm.thm("map_app_assoc"),
  ]
  let lh2_cases = @tactics.struct_cases_tac(
    @bool.spec(tm("(lh2 : Lholed)"), @ind_types.cases("lholed")),
  )
  let case_tac = seq([
    lh2_cases,
    @simp.simp_tac(ths(normal + [thm("first_nonval_eq")] + is_val + ctor)),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @tactics.try_tac(
      @meson.asm_meson_tac(ths([thm("append_len_eq"), @arith.add_clauses()])),
    ),
  ])
  let ret = (vs : String) => "APPEND(MAP(v_to_e, \{vs}), [Basic(Return)])"
  let _ = lemma(
    "ret_unique",
    "∀ lh1 : Lholed, ∀ lh2 : Lholed, ∀ vs1 : List[Value], ∀ vs2 : List[Value], lfill(lh1, \{ret("vs1")}) == lfill(lh2, \{ret("vs2")}) → lh_depth(lh1) == lh_depth(lh2) && (LENGTH(vs1) == LENGTH(vs2) → vs1 == vs2)",
    @tactics.thenl(
      @tactics.then_tac(
        @tactics.match_mp_tac(@wasm.thm("lholed_induct")),
        @tactics.conj_tac,
      ),
      @list.List([
        seq([@tactics.repeat_tac(@tactics.gen_tac), case_tac]),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_tac,
          @tactics.repeat_tac(@tactics.gen_tac),
          case_tac,
        ]),
      ]),
    ),
  )
  let a = assn
  let _ = lemma(
    "ret_frame_case",
    "∀ lh : Lholed, ∀ lh2 : Lholed, ∀ vs : List[Value], ∀ vs2 : List[Value], ∀ m : Num, ∀ rin : \{a}, ∀ s : Wstore, ∀ f : Wframe, lfill(lh, \{ret("vs")}) == lfill(lh2, \{ret("vs2")}) && rin(s, f, vs) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ v : List[Value], rin(s2, f2, v) → LENGTH(v) == m) && LENGTH(vs2) == m → rin(s, f, vs2)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => {
        @tactics.mp_tac(@drule.match_mp(thm("ret_unique"))(th))
      }),
      have(
        "LENGTH((vs : List[Value])) == (m : Num)",
        @meson.asm_meson_tac(ths([])),
      ),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ]),
  )
}

///|
/// safer_label: label_safe with returns (a return inside the label is one
/// of the labelled code).
fn prove_safer_label() -> Unit raise {
  let a = assn
  let safer = thm("safer")
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
    @meson.asm_meson_tac(ths([le_suc])),
  ])
  let not_vals = seq([
    subst_vars(),
    @meson.asm_meson_tac(ths([thm("br_not_vals"), @wasm.thm("all_vals_map")])),
  ])
  let not_trap = seq([
    subst_vars(),
    @meson.asm_meson_tac(ths([thm("br_not_trap")])),
  ])
  let map_trap = [
    @wasm.thm("map_v_to_e_eq_cons"),
    @wasm.thm("eq_v_to_e"),
    einstr_d,
    @equal.gsym(einstr_d),
  ]
  let arith_suc = arith("∀ i : Num, ∀ d : Num, SUC(i) + d == i + (d + 1)")
  let arith_ne = arith("∀ i : Num, ∀ d : Num, !(d == SUC(i) + d)")
  let step3 = seq([@tactics.disj2_tac, @tactics.disj2_tac, @tactics.disj2_tac])
  let _ = lemma(
    "safer_label",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ qb : \{a}, ∀ lb : \{a}, ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, safer(n, s, f, li, qb, CONS(lb, l), rq) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], qb(s, f, vs) → q(s, f, APPEND(vs0, vs))) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ k : Num, k <= n → lb(s, f, vs) → LENGTH(vs) == m && safer(k, s, f, APPEND(MAP(v_to_e, vs0), APPEND(MAP(v_to_e, vs), e0)), q, l, rq)) → safer(n, s, f, APPEND(MAP(v_to_e, vs0), [\{label}]), q, l, rq)",
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
                      @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_vals")])),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([thm("map_v_to_e_inj")])),
                        ),
                        subst_vars(),
                        @simp.rewrite_tac(
                          ths([@equal.gsym(@lists.map_append())]),
                        ),
                        @tactics.match_mp_tac(thm("safer_vals")),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths(map_trap)),
                        ),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([lfilled_eq])),
                        ),
                        @meson.asm_meson_tac(
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
                      @meson.asm_meson_tac(ths([le_n_suc])),
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
                            subst_vars(),
                            have(
                              "(vs' : List[Value]) == (vs : List[Value])",
                              @meson.asm_meson_tac(ths([thm("br_unique")])),
                            ),
                            subst_vars(),
                            @meson.asm_meson_tac(ths([le_n_suc])),
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
                            subst_vars(),
                            @meson.asm_meson_tac(
                              ths([thm("br_unique"), arith_ne]),
                            ),
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
              // the body steps
              seq([
                @simp.rewrite_tac(ths([safer])),
                step3,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    @meson.asm_meson_tac(ths([thm("reduce_label")])),
                    steps([
                      inside,
                      seq([
                        subst_vars(),
                        @meson.asm_meson_tac(
                          ths([@wasm.thm("reduce_not_vals")]),
                        ),
                      ]),
                      seq([
                        subst_vars(),
                        @meson.asm_meson_tac(
                          ths([@wasm.thm("reduce_not_trap")]),
                        ),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([lfilled_eq])),
                        ),
                        subst_vars(),
                        @meson.asm_meson_tac(
                          ths([thm("br_stuck"), @arith.le_refl()]),
                        ),
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
  let _ = lemma(
    "safer_label_top",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ m : Num, ∀ li : List[Einstr], ∀ qb : \{a}, ∀ rb : \{a}, safer(n, s, f, li, qb, [qb], rb) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qb(s2, f2, vs) → LENGTH(vs) == m) → safer(n, s, f, [Label(m, NIL, li)], qb, NIL, rb)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            [
              "(n : Num)",
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
          thm("safer_label"),
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
          solve(@meson.asm_meson_tac(ths([]))),
          solve(
            seq([
              @tactics.match_mp_tac(thm("safer_vals")),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
        ]),
      ),
    ]),
  )
}

///|
/// A frame with returns: its content's values, or a return's, leave it.
fn prove_safer_frame() -> Unit raise {
  let a = assn
  let safer = thm("safer")
  let rs = @wasm.thm("reduce_simple_rules")
  let rb = @wasm.thm("reduce_base_rules")
  let frame_vals = {
    let mut found = None
    for r in @bool.conjuncts_rule(rs) {
      let c = @basics.strip_forall(@kernel.concl(r)).1
      let text = show(c)
      if !@basics.is_imp(c) && text.contains("Frame(") && !text.contains("Trap") {
        found = Some(r)
      }
    }
    guard found is Some(r) else {
      raise Failure("wasmcert/logic: no frame rule")
    }
    r
  }
  let frame_ret = rule_with(rs, ["Frame(", "Return"])
  let rb_lift = @bool.conjuncts_rule(rb).to_array()[0]
  let rb_frame = rule_with(rb, ["Frame(", "reduce("])
  let after_vals = thm("reduce_after_vals")
  let frame = "Frame((m : Num), (f1 : Wframe), (es : List[Einstr]))"
  let code = "APPEND(MAP(v_to_e, (vs0 : List[Value])), [\{frame}])"
  let no_br = [safer, @lists.length(), arith("∀ i : Num, !(i < 0)")]
  let rin_len = "(∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], rin(s2, f2, vs) → LENGTH(vs) == m)"
  let can_step = lemma(
    "frame_can_step_r",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, safer(SUC(n), s, f1, es, qin, NIL, rin) && \{rin_len} → (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f0, \{code}, s2, f2, es2))",
    seq([
      @simp.rewrite_tac(ths(no_br)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.first(
        @list.List([
          // the content is values: the frame leaves with them
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(
                tm(
                  "APPEND(MAP(v_to_e, (vs0 : List[Value])), MAP(v_to_e, (vs : List[Value])))",
                ),
              ),
              @tactics.match_mp_tac(after_vals),
              @tactics.match_mp_tac(rb_lift),
              @tactics.match_accept_tac(frame_vals),
            ]),
          ),
          // a return: the frame leaves with its values
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(
                tm(
                  "APPEND(MAP(v_to_e, (vs0 : List[Value])), MAP(v_to_e, (vs : List[Value])))",
                ),
              ),
              @tactics.match_mp_tac(after_vals),
              @tactics.match_mp_tac(rb_lift),
              @tactics.match_mp_tac(frame_ret),
              @tactics.exists_tac(tm("lh_depth((lh : Lholed))")),
              @tactics.exists_tac(tm("(lh : Lholed)")),
              @simp.rewrite_tac(ths([@wasm.thm("lfilled_lfill")])),
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
          // the content steps: so does the frame
          solve(
            seq([
              @tactics.exists_tac(tm("(s2 : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(
                tm(
                  "APPEND(MAP(v_to_e, (vs0 : List[Value])), [Frame((m : Num), (f2 : Wframe), (es2 : List[Einstr]))])",
                ),
              ),
              @tactics.match_mp_tac(after_vals),
              @tactics.match_mp_tac(rb_frame),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let vals_not_trap = thm("vals_not_trap")
  let ret_not_map = thm("ret_not_map")
  let ret_not_trap = thm("ret_not_trap")
  let impossible = [
    @wasm.thm("reduce_not_vals"),
    @wasm.thm("reduce_not_trap"),
    thm("return_stuck"),
    vals_not_trap,
    @equal.gsym(vals_not_trap),
    ret_not_map,
    @equal.gsym(ret_not_map),
    ret_not_trap,
    @equal.gsym(ret_not_trap),
  ]
  let next = lemma(
    "frame_next_r",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], safer(SUC(n), s, f1, es, qin, NIL, rin) && reduce(s, f0, \{code}, s2, f2, es2) && \{rin_len} → (∃ f1' : Wframe, ∃ es' : List[Einstr], safer(n, s2, f1', es', qin, NIL, rin) && f2 == f0 && es2 == APPEND(MAP(v_to_e, vs0), [Frame(m, f1', es')])) || (s2 == s && f2 == f0 && (∃ vs : List[Value], es2 == MAP(v_to_e, APPEND(vs0, vs)) && (qin(s, f1, vs) || rin(s, f1, vs))))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(
        @tactics.conjuncts_then2(
          c => @tactics.strip_assume_tac(@simp.rewrite_rule(ths(no_br))(c)),
          c => {
            @tactics.conjuncts_then2(
              c1 => {
                @tactics.strip_assume_tac(
                  @drule.match_mp(thm("frame_steps"))(c1),
                )
              },
              c2 => @tactics.assume_tac(c2),
            )(c)
          },
        ),
      ),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([@wasm.thm("lfilled_eq"), thm("map_v_to_e_inj")]),
        ),
      ),
      split_conjs(),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(impossible))),
      @tactics.try_tac(@tactics.first_assum(th => @tactics.contr_tac(th))),
      @tactics.first(
        @list.List([
          // a step inside
          solve(
            seq([
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(f1' : Wframe)")),
              @tactics.exists_tac(tm("(es' : List[Einstr])")),
              @simp.asm_rewrite_tac(ths([])),
              @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
          // out, with the values
          solve(
            seq([
              @tactics.disj2_tac,
              @simp.asm_rewrite_tac(ths([@lists.map_append()])),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          // out, with a return's values
          solve(
            seq([
              @tactics.disj2_tac,
              @simp.asm_rewrite_tac(ths([@lists.map_append()])),
              @meson.asm_meson_tac(ths([thm("ret_frame_case")])),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "frame_safe_r",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, ∀ q : \{a}, ∀ l : List[\{a}], ∀ rq : \{a}, safer(n, s, f1, es, qin, NIL, rin) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs2 : List[Value], qin(s2, f2, vs2) → q(s2, f0, APPEND(vs0, vs2))) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs2 : List[Value], rin(s2, f2, vs2) → LENGTH(vs2) == m && q(s2, f0, APPEND(vs0, vs2))) → safer(n, s, f0, \{code}, q, l, rq)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safer])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          have(rin_len, @meson.asm_meson_tac(ths([]))),
          @tactics.conv_tac(@simp.once_rewrite_conv(ths([safer]))),
          @tactics.disj2_tac,
          @tactics.disj2_tac,
          @tactics.disj2_tac,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @meson.asm_meson_tac(ths([can_step])),
              seq([
                @tactics.repeat_tac(@tactics.strip_tac),
                forward2_3(next),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_vars(),
                @tactics.first(
                  @list.List([
                    // still inside the frame
                    solve(
                      seq([
                        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                    ),
                    // out of it, with values
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safer_vals")),
                        @meson.asm_meson_tac(ths([])),
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
