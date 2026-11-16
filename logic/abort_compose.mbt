// Composition retains the same specified abort state in either component.

///|
fn prove_abort_composition() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let inst = (th : @kernel.Thm, xs : Array[String]) => {
    @bool.ispecl(@list.List(xs.map(tm)), th)
  }
  let sa = thm("safe_abort")
  let literal = @tactics.prove(
    tm("trap_top([Trap])"),
    seq([
      rw([@wasm.thm("trap_top")]),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.exists_tac(tm("(NIL : List[Einstr])")),
      rw([@lists.map(), @lists.append()]),
    ]),
  )
  let _ = lemma(
    "safe_abort_trap_assert",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, ∀ a : \{at}, safe_abort(SUC(n),s,f,[Trap],q,a) → a(s,f)",
    seq([
      rw([sa, thm("vals_not_trap"), @wasm.thm("reduce_not_trap")]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "safe_abort_top_assert",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ a : \{at}, (∀ k : Num, safe_abort(k,s,f,es,q,a)) && trap_top(es) → a(s,f)",
    seq([
      gen,
      strip,
      @class.asm_cases_tac(tm("(es : List[Einstr]) == [Trap]")),
      @tactics.first(
        @list.List([
          solve(
            seq([
              subst_vars(),
              @meson.asm_meson_tac(ths([thm("safe_abort_trap_assert")])),
            ]),
          ),
          solve(
            seq([
              have(
                "reduce((s : Wstore),(f : Wframe),(es : List[Einstr]),s,f,[Trap])",
                seq([@tactics.match_mp_tac(thm("trap_step")), arw([])]),
              ),
              have(
                "safe_abort(SUC(0),(s : Wstore),(f : Wframe),[Trap],(q : \{assn}),(a : \{at}))",
                @meson.asm_meson_tac(ths([thm("safe_abort_after_step")])),
              ),
              @meson.asm_meson_tac(ths([thm("safe_abort_trap_assert")])),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : \{assn}, ∀ r : \{assn}, ∀ a : \{at}"
  let source = "∀ k : Num, safe_abort(k,(s : Wstore),(f : Wframe),(es1 : List[Einstr]),(q : \{assn}),(a : \{at}))"
  let _ = lemma(
    "safe_abort_seq_all",
    "∀ n : Num, \{vars}, (\{source}) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], ∀ k : Num, q(s2,f2,vs) → safe_abort(k,s2,f2,APPEND(MAP(v_to_e,vs),es2),r,a)) → safe_abort(n,s,f,APPEND(es1,es2),r,a)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        rw([sa]),
        seq([
          gen,
          strip,
          @tactics.thenl(
            @class.asm_cases_tac(tm("trap_top((es1 : List[Einstr]))")),
            @list.List([
              seq([
                @tactics.match_mp_tac(thm("safe_abort_top_trap")),
                @meson.asm_meson_tac(
                  ths([
                    thm("safe_abort_top_assert"),
                    thm("abort_trap_append"),
                    thm("abort_trap_nonvalues"),
                  ]),
                ),
              ]),
              seq([
                @tactics.mp_tac(
                  @bool.spec(tm("SUC(0)"), @kernel.assume_rule(tm(source))),
                ),
                @tactics.conv_tac(
                  @equal.rator_conv(
                    @equal.rand_conv(@simp.pure_once_rewrite_conv(ths([sa]))),
                  ),
                ),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_vars(),
                @tactics.first(
                  @list.List([
                    solve(@meson.asm_meson_tac(ths([literal]))),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_step")),
                        @tactics.thenl(
                          @tactics.conj_tac,
                          @list.List([
                            @meson.asm_meson_tac(ths([thm("reduce_app")])),
                            seq([
                              @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                              @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                              @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                              @tactics.disch_tac,
                              have(
                                "!ALL(is_val,(es1 : List[Einstr]))",
                                @meson.asm_meson_tac(
                                  ths([@wasm.thm("reduce_ok")]),
                                ),
                              ),
                              @tactics.mp_tac(
                                inst(@wasm.thm("reduce_append"), [
                                  "(s : Wstore)", "(f : Wframe)", "(es1 : List[Einstr])",
                                  "(es2 : List[Einstr])", "(t1 : Wstore)", "(t2 : Wframe)",
                                  "(t3 : List[Einstr])",
                                ]),
                              ),
                              arw([]),
                              strip,
                              subst_vars(),
                              @tactics.first_x_assum(th => {
                                @tactics.match_mp_tac(th)
                              }),
                              @tactics.exists_tac(tm("(q : \{assn})")),
                              @tactics.conj_tac,
                              @tactics.first(
                                @list.List([
                                  solve(
                                    seq([
                                      gen,
                                      @meson.asm_meson_tac(
                                        ths([thm("safe_abort_after_step")]),
                                      ),
                                    ]),
                                  ),
                                  solve(arw([])),
                                ]),
                              ),
                            ]),
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
