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
}
