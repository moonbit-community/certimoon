// Adequacy: what a triple says about runs, with reduce_trans alone.
//
// A triple is defined through safe (or safel), safety for n steps. The
// theorems here state its meaning without them: from a state satisfying
// the precondition, every run (reduce_trans, any number of steps) reaches
// a configuration that is either values satisfying the postcondition or
// can step again. So no run traps ([Trap] is not values and does not
// step) or gets stuck. These are the statements to read to trust what a
// triple claims; safe, safel, triple and triple_l are not needed for that.
//
// - safe_step: a step from a configuration safe for n + 1 steps is safe
//   for n.
// - safe_run: safety for every n carries along a run.
// - safe_adequate: the end of a run from a configuration safe for every n
//   is values satisfying q, or can step.
// - sl_triple_adequate, sl_triple_m_adequate: the same for the code of a
//   triple, from a state with the precondition (lifted with a frame r).
//   sl_triple_m's is for triples with no labels, as the examples' are,
//   and states keep's conditions (the store's functions, the frame's
//   instance) written out.
// - sl_triple_m_adequate_whole: the same with no frame (r is emp): the
//   precondition holds of the whole memory j of the instance, and so does
//   the postcondition at the end. No heap assertion is left in it, only
//   the precondition and postcondition applied to the state's parts.
//   star_emp_r and lift_emp are its lemmas.
// - arr_in_mem: an array with the bytes before and after it is the
//   memory's bytes, as a list, so a closed theorem can state memory
//   without heaps (heap_of_pts_heap, pts_heap_eq).

///|
fn prove_adequacy() -> Unit raise {
  let safe = thm("safe")
  let cfg = "(Wstore, Wframe, List[Einstr])"
  let safe_step = lemma(
    "safe_step",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], safe(SUC(n), s, f, es, q) && reduce(s, f, es, s2, f2, es2) → safe(n, s2, f2, es2, q)",
    seq([
      @simp.rewrite_tac(ths([safe])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_vals")])),
    ]),
  )
  let safe_run = lemma(
    "safe_run",
    "∀ c : \{cfg}, ∀ c2 : \{cfg}, reduce_trans(c, c2) → (∀ q : \{assn}, (∀ n : Num, safe(n, FST(c), FST(SND(c)), SND(SND(c)), q)) → (∀ n : Num, safe(n, FST(c2), FST(SND(c2)), SND(SND(c2)), q)))",
    seq([
      @tactics.match_mp_tac(@wasm.thm("reduce_trans_induct")),
      beta_goal(),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          @meson.meson_tac(ths([])),
          seq([
            @simp.rewrite_tac(ths([@pair.fst(), @pair.snd()])),
            @tactics.repeat_tac(@tactics.strip_tac),
            @meson.asm_meson_tac(ths([safe_step])),
          ]),
        ]),
      ),
    ]),
  )
  let safe_progress = lemma(
    "safe_progress",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, safe(SUC(0), s, f, es, q) → (∃ vs : List[Value], es == MAP(v_to_e, vs) && q(s, f, vs)) || (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2))",
    seq([@simp.rewrite_tac(ths([safe])), @meson.meson_tac(ths([]))]),
  )
  let safe_adequate = lemma(
    "safe_adequate",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], (∀ n : Num, safe(n, s, f, es, q)) && reduce_trans((s, f, es), (s2, f2, es2)) → (∃ vs : List[Value], es2 == MAP(v_to_e, vs) && q(s2, f2, vs)) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "∀ n : Num, safe(n, (s2 : Wstore), (f2 : Wframe), (es2 : List[Einstr]), (q : \{assn}))",
        seq([
          @tactics.mp_tac(
            @bool.ispecl(
              @list.List([
                tm("((s : Wstore), (f : Wframe), (es : List[Einstr]))"),
                tm("((s2 : Wstore), (f2 : Wframe), (es2 : List[Einstr]))"),
              ]),
              safe_run,
            ),
          ),
          @simp.rewrite_tac(ths([@pair.fst(), @pair.snd()])),
          @meson.asm_meson_tac(ths([])),
        ]),
      ),
      @meson.asm_meson_tac(ths([safe_progress])),
    ]),
  )
  let code = "APPEND(MAP(v_to_e, (vs : List[Value])), MAP(Basic, (bs : List[B_e])))"
  // safe_adequate for the code from (s, f, vs), with postcondition post
  let adequate_at = (post : String) => @bool.ispecl(
    @list.List([tm("(s : Wstore)"), tm("(f : Wframe)"), tm(code), tm(post)]),
    safe_adequate,
  )
  let _ = lemma(
    "sl_triple_adequate",
    "∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ r : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], sl_triple(p, bs, q) && lift(p, r, s, f, vs) && reduce_trans((s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs))), (s2, f2, es2)) → (∃ vs2 : List[Value], es2 == MAP(v_to_e, vs2) && lift(q, r, s2, f2, vs2)) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "∀ n : Num, safe(n, (s : Wstore), (f : Wframe), \{code}, lift((q : \{sassn}), (r : \{hprop})))",
        @meson.asm_meson_tac(ths([])),
      ),
      @tactics.mp_tac(adequate_at("lift((q : \{sassn}), (r : \{hprop}))")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_triple_m_adequate",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ r : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], sl_triple_m(fs, inst, p, bs, q, NIL) && s_funcs(s) == fs && f_inst(f) == inst && lift(p, r, s, f, vs) && reduce_trans((s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs))), (s2, f2, es2)) → (∃ vs2 : List[Value], es2 == MAP(v_to_e, vs2) && s_funcs(s2) == fs && f_inst(f2) == inst && lift(q, r, s2, f2, vs2)) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple_m"), thm("triple_l"), @lists.map()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "∀ n : Num, safe(n, (s : Wstore), (f : Wframe), \{code}, keep((fs : List[Cl]), (inst : Inst), lift((q : \{sassn}), (r : \{hprop}))))",
        seq([
          @tactics.gen_tac,
          @tactics.match_mp_tac(thm("safel_nil")),
          @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
          @simp.asm_rewrite_tac(ths([thm("keep")])),
        ]),
      ),
      @tactics.mp_tac(adequate_at("keep((fs : List[Cl]), (inst : Inst), lift((q : \{sassn}), (r : \{hprop})))")),
      @simp.rewrite_tac(ths([thm("keep")])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let opt = [@ind_types.option_distinct(), @equal.gsym(@ind_types.option_distinct()), @ind_types.option_inj()]
  let hunion_emp = lemma(
    "hunion_emp",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, (∀ x : Num, h2(x) == NONE) → hunion(h1, h2) == h1",
    seq([
      @simp.rewrite_tac(ths([thm("hunion"), @class.fun_eq_thm()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.try_tac(@tactics.then_tac(@class.cond_cases_tac, @simp.asm_rewrite_tac(ths(opt)))),
    ]),
  )
  let star_emp_r = lemma(
    "star_emp_r",
    "∀ p : \{hprop}, ∀ h : \{heap}, star(p, emp, h) == p(h)",
    seq([
      @simp.rewrite_tac(ths([thm("star"), thm("emp")])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.thenl(
        @tactics.eq_tac,
        @list.List([
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            have(
              "hunion((h1 : \{heap}), (h2 : \{heap})) == h1",
              seq([@tactics.match_mp_tac(hunion_emp), @simp.asm_rewrite_tac(ths([]))]),
            ),
            @meson.asm_meson_tac(ths([])),
          ]),
          seq([
            @tactics.strip_tac,
            @tactics.exists_tac(tm("(h : \{heap})")),
            @tactics.exists_tac(tm("(((x : Num) => NONE) : \{heap})")),
            have(
              "hunion((h : \{heap}), (((x : Num) => NONE) : \{heap})) == h",
              seq([@tactics.match_mp_tac(hunion_emp), beta_goal(), @simp.rewrite_tac(ths([]))]),
            ),
            @simp.asm_rewrite_tac(ths([thm("hdisj")])),
          ]),
        ]),
      ),
    ]),
  )
  let lift_emp = lemma(
    "lift_emp",
    "∀ p : \{sassn}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], lift(p, emp, s, f, vs) == (∃ j : Num, smem_ind(f_inst(f)) == SOME(j) && j < LENGTH(s_mems(s)) && globs_ok(s, f) && p(vs, f_locs(f), gvals(s, f), mem_length(EL(j, s_mems(s))), heap_of(EL(j, s_mems(s)))))",
    @simp.rewrite_tac(ths([thm("lift"), star_emp_r])),
  )
  let _ = lemma(
    "sl_triple_m_adequate_whole",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ j : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], sl_triple_m(fs, inst, p, bs, q, NIL) && s_funcs(s) == fs && f_inst(f) == inst && smem_ind(inst) == SOME(j) && j < LENGTH(s_mems(s)) && globs_ok(s, f) && p(vs, f_locs(f), gvals(s, f), mem_length(EL(j, s_mems(s))), heap_of(EL(j, s_mems(s)))) && reduce_trans((s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs))), (s2, f2, es2)) → (∃ vs2 : List[Value], es2 == MAP(v_to_e, vs2) && s_funcs(s2) == fs && f_inst(f2) == inst && j < LENGTH(s_mems(s2)) && globs_ok(s2, f2) && q(vs2, f_locs(f2), gvals(s2, f2), mem_length(EL(j, s_mems(s2))), heap_of(EL(j, s_mems(s2))))) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            [
              "(fs : List[Cl])", "(inst : Inst)", "(p : \{sassn})", "(bs : List[B_e])", "(q : \{sassn})",
              "emp", "(s : Wstore)", "(f : Wframe)", "(vs : List[Value])", "(s2 : Wstore)", "(f2 : Wframe)",
              "(es2 : List[Einstr])",
            ].map(tm),
          ),
          thm("sl_triple_m_adequate"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([lift_emp] + opt)),
      @meson.asm_meson_tac(ths(opt)),
    ]),
  )
  // A closed theorem states a memory as its list of bytes
  let heap_of_pts_heap = lemma(
    "heap_of_pts_heap",
    "∀ m : \{mem_ty}, heap_of(m) == pts_heap(0, SND(m))",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([thm("heap_of"), thm("pts_heap"), @arith.le_0(), @arith.add_clauses(), @arith.sub_0()])),
    ]),
  )
  let pts_heap_unfold = ths([thm("pts_heap"), @arith.le_0(), @arith.add_clauses(), @arith.sub_0(), @arith.lt_refl()])
  let pts_heap_eq = lemma(
    "pts_heap_eq",
    "∀ bs : List[\{w8}], ∀ cs : List[\{w8}], (pts_heap(0, bs) == pts_heap(0, cs)) == (bs == cs)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.thenl(
        @tactics.eq_tac,
        @list.List([
          seq([
            @simp.rewrite_tac(ths([@class.fun_eq_thm()])),
            @tactics.disch_tac,
            // the lengths agree: at the shorter list's length, one side is NONE
            have(
              "LENGTH((bs : List[\{w8}])) == LENGTH((cs : List[\{w8}]))",
              seq([
                @tactics.first_assum(th => @tactics.mp_tac(@bool.spec(tm("LENGTH((bs : List[\{w8}]))"), th))),
                @tactics.first_assum(th => @tactics.mp_tac(@bool.spec(tm("LENGTH((cs : List[\{w8}]))"), th))),
                @simp.rewrite_tac(pts_heap_unfold),
                @tactics.repeat_tac(@tactics.then_tac(@class.cond_cases_tac, @simp.rewrite_tac(ths(opt)))),
                @tactics.try_tac(@int.asm_arith_tac),
              ]),
            ),
            @simp.pure_once_rewrite_tac(ths([@lists.list_eq()])),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.x_gen_tac(tm("(i : Num)")),
            @tactics.disch_tac,
            @tactics.first_assum(th => @tactics.mp_tac(@bool.spec(tm("(i : Num)"), th))),
            @simp.rewrite_tac(pts_heap_unfold),
            @simp.asm_rewrite_tac(ths(opt)),
          ]),
          seq([@tactics.disch_tac, @simp.asm_rewrite_tac(ths([]))]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "arr_in_mem",
    "∀ a : Num, ∀ k : Num, ∀ before : List[\{w8}], ∀ ys : List[\{w32}], ∀ after : List[\{w8}], ∀ m : \{mem_ty}, LENGTH(before) == a && LENGTH(ys) == k → (star(arr(a, ys), star(pts(0, before), pts(a + 4 * k, after)), heap_of(m)) == (SND(m) == APPEND(before, APPEND(words_bytes(ys), after))))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      have(
        "star(arr((a : Num), (ys : List[\{w32}])), star(pts(0, (before : List[\{w8}])), pts(a + 4 * (k : Num), (after : List[\{w8}])))) == pts(0, APPEND(before, APPEND(words_bytes(ys), after)))",
        seq([
          @simp.rewrite_tac(ths([thm("arr"), thm("pts_split"), @arith.add_clauses(), thm("length_words_bytes")])),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.match_accept_tac(thm("star_left_comm")),
        ]),
      ),
      @simp.asm_rewrite_tac(ths([])),
      @simp.rewrite_tac(ths([thm("pts"), heap_of_pts_heap, pts_heap_eq])),
    ]),
  )
}
