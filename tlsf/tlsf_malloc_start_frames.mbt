// Native frames restore the caller on normal returns and initialization aborts.

///|
fn prove_tlsf_start_frames() -> Unit raise {
  let a = @logic.assn
  let safer = thm("tlsf_safer_abort")
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
      raise Failure("certimoon/logic: no frame rule")
    }
    r
  }
  let frame_trap = startup_rule_with(rs, ["Frame(", "Trap"])
  let frame_ret = startup_rule_with(rs, ["Frame(", "Return"])
  let rb_lift = @bool.conjuncts_rule(rb).to_array()[0]
  let rb_frame = startup_rule_with(rb, ["Frame(", "reduce("])
  let after_vals = thm("reduce_after_vals")
  let frame = "Frame((m : Num), (f1 : Wframe), (es : List[Einstr]))"
  let code = "APPEND(MAP(v_to_e, (vs0 : List[Value])), [\{frame}])"
  let no_br = [safer, @lists.length(), arith("∀ i : Num, !(i < 0)")]
  let rin_len = "(∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], rin(s2, f2, vs) → LENGTH(vs) == m)"
  let can_step = startup_lemma(
    "tlsf_frame_abort_can_step",
    "∀ n : Num, ∀ ab : (Wstore,Wframe) -> Bool, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, tlsf_safer_abort(SUC(n), s, f1, es, qin, NIL, rin, (ab : (Wstore,Wframe) -> Bool)) && \{rin_len} → (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f0, \{code}, s2, f2, es2))",
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
              startup_meson(ths([])),
            ]),
          ),
          // A specified trap leaves the frame, retaining the caller's locals.
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(
                tm("APPEND(MAP(v_to_e,(vs0 : List[Value])),[Trap])"),
              ),
              @tactics.match_mp_tac(after_vals),
              @tactics.match_mp_tac(rb_lift),
              @tactics.match_accept_tac(frame_trap),
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
  let next = startup_lemma(
    "tlsf_frame_abort_next",
    "∀ n : Num, ∀ ab : (Wstore,Wframe) -> Bool, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], tlsf_safer_abort(SUC(n), s, f1, es, qin, NIL, rin, (ab : (Wstore,Wframe) -> Bool)) && reduce(s, f0, \{code}, s2, f2, es2) && \{rin_len} → (∃ f1' : Wframe, ∃ es' : List[Einstr], tlsf_safer_abort(n, s2, f1', es', qin, NIL, rin, (ab : (Wstore,Wframe) -> Bool)) && f2 == f0 && es2 == APPEND(MAP(v_to_e, vs0), [Frame(m, f1', es')])) || (s2 == s && f2 == f0 && (∃ vs : List[Value], es2 == MAP(v_to_e, APPEND(vs0, vs)) && (qin(s, f1, vs) || rin(s, f1, vs)))) || (s2 == s && f2 == f0 && es2 == APPEND(MAP(v_to_e,vs0),[Trap]) && ab(s,f1))",
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
              @tactics.disj1_tac,
              @simp.asm_rewrite_tac(ths([@lists.map_append()])),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          solve(
            seq([
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          // out, with a return's values
          solve(
            seq([
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @simp.asm_rewrite_tac(ths([@lists.map_append()])),
              @meson.gen_meson_tac(0L, 16L, 1L, ths([thm("ret_frame_case")])),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_frame_abort_safe",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ rin : \{a}, ∀ ain : (Wstore,Wframe) -> Bool, ∀ q : \{a}, ∀ ab : (Wstore,Wframe) -> Bool, tlsf_safer_abort(n,s,f1,es,qin,NIL,rin,ain) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs2 : List[Value], qin(s2,f2,vs2) → q(s2,f0,APPEND(vs0,vs2))) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs2 : List[Value], rin(s2,f2,vs2) → LENGTH(vs2) == m && q(s2,f0,APPEND(vs0,vs2))) && (∀ s2 : Wstore, ∀ f2 : Wframe, ain(s2,f2) → ab(s2,f0)) → safe_abort(n,s,f0,\{code},q,ab)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([thm("safe_abort")])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          have(rin_len, startup_meson(ths([]))),
          @tactics.match_mp_tac(thm("safe_abort_step")),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              startup_meson(ths([can_step])),
              seq([
                @tactics.repeat_tac(@tactics.strip_tac),
                startup_forward(next),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_vars(),
                @tactics.first(
                  @list.List([
                    solve(
                      seq([
                        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                        @tactics.exists_tac(tm("(qin : \{a})")),
                        @tactics.exists_tac(tm("(rin : \{a})")),
                        @tactics.exists_tac(
                          tm("(ain : (Wstore,Wframe) -> Bool)"),
                        ),
                        startup_meson(ths([])),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_vals")),
                        startup_meson(ths([])),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_top_trap")),
                        startup_meson(
                          ths([
                            thm("abort_trap_drop_values"),
                            thm("tlsf_start_literal_trap"),
                          ]),
                        ),
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
