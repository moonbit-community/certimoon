// Labels propagate a specified trap without changing its store or frame.

///|
fn prove_abort_labels() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let inst = (th : @kernel.Thm, xs : Array[String]) => {
    @bool.ispecl(@list.List(xs.map(tm)), th)
  }
  let sa = thm("safe_abort")
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let _ = lemma(
    "abort_reduce_simple",
    "∀ s : Wstore, ∀ f : Wframe, ∀ e : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(e,e2) → reduce(s,f,e,s,f,e2)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("reduce_after_vals"), [
          "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(e : List[Einstr])",
          "(s : Wstore)", "(f : Wframe)", "(e2 : List[Einstr])",
        ]),
      ),
      rw([@lists.map(), @lists.append()]),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @tactics.match_mp_tac(rb),
      arw([]),
    ]),
  )
  let vs = "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ m : Num, ∀ e0 : List[Einstr], ∀ q : \{assn}, ∀ a : \{at}"
  let _ = lemma(
    "safe_abort_label_can_step",
    "\{vs}, safe_abort(SUC(n),s,f,es,q,a) → (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,[Label(m,e0,es)],s2,f2,es2))",
    seq([
      rw([sa]),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f : Wframe)")),
              @tactics.exists_tac(tm("MAP(v_to_e,(vs : List[Value]))")),
              @tactics.match_mp_tac(thm("abort_reduce_simple")),
              @tactics.match_accept_tac(rs[27]),
            ]),
          ),
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f : Wframe)")),
              @tactics.exists_tac(tm("([Trap] : List[Einstr])")),
              @tactics.match_mp_tac(thm("abort_reduce_simple")),
              @tactics.match_accept_tac(rs[28]),
            ]),
          ),
          solve(
            seq([
              @tactics.exists_tac(tm("(s2 : Wstore)")),
              @tactics.exists_tac(tm("(f2 : Wframe)")),
              @tactics.exists_tac(
                tm(
                  "[Label((m : Num),(e0 : List[Einstr]),(es2 : List[Einstr]))]",
                ),
              ),
              @tactics.match_mp_tac(
                @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
                  inst(thm("reduce_label"), [
                    "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(m : Num)",
                    "(e0 : List[Einstr])", "(es : List[Einstr])", "(s2 : Wstore)",
                    "(f2 : Wframe)", "(es2 : List[Einstr])",
                  ]),
                ),
              ),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let steps = @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
    inst(thm("label_steps"), [
      "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(m : Num)", "(e0 : List[Einstr])",
      "(es : List[Einstr])", "(s2 : Wstore)", "(f2 : Wframe)", "(es2 : List[Einstr])",
    ]),
  )
  let _ = lemma(
    "safe_abort_label",
    "\{vs}, safe_abort(n,s,f,es,q,a) → safe_abort(n,s,f,[Label(m,e0,es)],q,a)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        rw([sa]),
        seq([
          gen,
          @tactics.disch_tac,
          @tactics.match_mp_tac(thm("safe_abort_step")),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @meson.asm_meson_tac(ths([thm("safe_abort_label_can_step")])),
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
                        @meson.asm_meson_tac(
                          ths([thm("safe_abort_after_step")]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_vals")),
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([sa]))),
                        @meson.asm_meson_tac(
                          ths([
                            thm("map_v_to_e_inj"),
                            thm("vals_not_trap"),
                            @wasm.thm("reduce_not_vals"),
                          ]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.match_mp_tac(thm("safe_abort_trap")),
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([sa]))),
                        @meson.asm_meson_tac(
                          ths([
                            thm("vals_not_trap"),
                            @wasm.thm("reduce_not_trap"),
                          ]),
                        ),
                      ]),
                    ),
                    solve(
                      seq([
                        @tactics.rule_assum_tac(
                          @simp.rewrite_rule(ths([sa, @wasm.thm("lfilled_eq")])),
                        ),
                        subst_vars(),
                        @meson.asm_meson_tac(
                          ths([
                            thm("br_not_vals"),
                            thm("br_not_trap"),
                            thm("br_stuck"),
                            @arith.le_refl(),
                            @wasm.thm("all_vals_map"),
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
