// Native frames propagate normal values and the specified abort state.

///|
fn prove_abort_frames() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let inst = (th : @kernel.Thm, xs : Array[String]) => {
    @bool.ispecl(@list.List(xs.map(tm)), th)
  }
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let context = @bool.conjuncts_rule(@wasm.thm("reduce_rules")).to_array()[39]
  let _ = lemma(
    "safe_abort_values_assert",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : \{assn}, ∀ a : \{at}, safe_abort(SUC(n),s,f,MAP(v_to_e,vs),q,a) → q(s,f,vs)",
    seq([
      rw([thm("safe_abort")]),
      @meson.meson_tac(
        ths([
          thm("map_v_to_e_inj"),
          thm("vals_not_trap"),
          @wasm.thm("reduce_not_vals"),
        ]),
      ),
    ]),
  )
  let vars = "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{assn}, ∀ ain : \{at}"
  let frame = "[Frame((m : Num),(f1 : Wframe),(es : List[Einstr]))]"
  let _ = lemma(
    "safe_abort_frame_can_step",
    "\{vars}, safe_abort(SUC(n),s,f1,es,qin,ain) → (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f0,\{frame},s2,f2,es2))",
    seq([
      rw([thm("safe_abort")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(tm("MAP(v_to_e,(vs : List[Value]))")),
              @tactics.match_mp_tac(thm("abort_reduce_simple")),
              @tactics.match_accept_tac(rs[34]),
            ]),
          ),
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(tm("([Trap] : List[Einstr])")),
              @tactics.match_mp_tac(thm("abort_reduce_simple")),
              @tactics.match_accept_tac(rs[35]),
            ]),
          ),
          solve(
            seq([
              @tactics.exists_tac(tm("(s2 : Wstore)")),
              @tactics.exists_tac(tm("(f0 : Wframe)")),
              @tactics.exists_tac(
                tm("[Frame((m : Num),(f2 : Wframe),(es2 : List[Einstr]))]"),
              ),
              @tactics.match_mp_tac(context),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let steps = @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
    inst(thm("frame_steps"), [
      "(s : Wstore)", "(f0 : Wframe)", "(NIL : List[Value])", "(m : Num)", "(f1 : Wframe)",
      "(es : List[Einstr])", "(s2 : Wstore)", "(f2 : Wframe)", "(es2 : List[Einstr])",
    ]),
  )
  let transfer = "(∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qin(s2,f2,vs) → q(s2,f0,vs)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ain(s2,f2) → a(s2,f0))"
  let _ = lemma(
    "safe_abort_frame",
    "\{vars}, ∀ q : \{assn}, ∀ a : \{at}, safe_abort(n,s,f1,es,qin,ain) && \{transfer} → safe_abort(n,s,f0,\{frame},q,a)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        rw([thm("safe_abort")]),
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.match_mp_tac(thm("safe_abort_step")),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @meson.asm_meson_tac(ths([thm("safe_abort_frame_can_step")])),
              seq([
                gen,
                @tactics.disch_then(th => {
                  @tactics.strip_assume_tac(@drule.match_mp(steps)(th))
                }),
                subst_vars(),
                @tactics.first(
                  @list.List([
                    solve(
                      seq([
                        @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                        @tactics.exists_tac(tm("(qin : \{assn})")),
                        @tactics.exists_tac(tm("(ain : \{at})")),
                        @meson.asm_meson_tac(
                          ths([thm("safe_abort_after_step")]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_vals")),
                        @meson.asm_meson_tac(
                          ths([thm("safe_abort_values_assert")]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_trap")),
                        @meson.asm_meson_tac(
                          ths([thm("safe_abort_trap_assert")]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(
                            ths([thm("safe_abort"), @wasm.thm("lfilled_eq")]),
                          ),
                        ),
                        subst_vars(),
                        @meson.asm_meson_tac(
                          ths([
                            thm("ret_not_map"),
                            thm("ret_not_trap"),
                            thm("return_stuck"),
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
