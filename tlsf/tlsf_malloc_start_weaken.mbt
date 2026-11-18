// Allocation bodies have one enclosing result label. Weaken its assertion
// together with the return, normal, and abort assertions at the export boundary.

///|
fn prove_tlsf_start_weaken() -> Unit raise {
  let sa = sassn
  let env = startup_env()
  let ent = (p : String, q : String) => {
    "(∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", " +
    p +
    "(vs,lc,gs,ms,h) → " +
    q +
    "(vs,lc,gs,ms,h))"
  }
  let keep = (p : String) => {
    "keep(" + env + ",lift((" + p + " : " + sa + "),(fr : " + hprop + ")))"
  }
  let _ = startup_lemma(
    "tlsf_sl_abort_r_weaken",
    startup_quant() +
    "∀ rp : " +
    sa +
    ", ∀ rp2 : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ P2 : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ Q2 : " +
    sa +
    ", ∀ L : " +
    sa +
    ", ∀ L2 : " +
    sa +
    ", ∀ A : " +
    sa +
    ", ∀ A2 : " +
    sa +
    ", " +
    ent("P2", "P") +
    " && tlsf_sl_abort_r(" +
    env +
    ",rp,P,bs,Q,[L],A) && " +
    ent("Q", "Q2") +
    " && " +
    ent("rp", "rp2") +
    " && " +
    ent("L", "L2") +
    " && " +
    ent("A", "A2") +
    " → tlsf_sl_abort_r(" +
    env +
    ",rp2,P2,bs,Q2,[L2],A2)",
    seq([
      @simp.rewrite_tac(ths([thm("tlsf_sl_abort_r"), @lists.map()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      g => {
        let a = args_of(g.1, "tlsf_safer_abort", 8).unwrap()
        let rule = inst(thm("tlsf_safer_abort_mono"), [
          show(a[0]),
          "(s : Wstore) => (f : Wframe) => " + keep("A") + "(s,f,NIL)",
          show(a[7]),
          show(a[1]),
          show(a[2]),
          show(a[3]),
          keep("Q"),
          show(a[4]),
          "[" + keep("L") + "]",
          show(a[5]),
          keep("rp"),
          show(a[6]),
        ])
        return seq([
          @tactics.match_mp_tac(rule),
          @simp.rewrite_tac(ths([@lists.length()])),
          @tactics.repeat_tac(@tactics.conj_tac),
          @tactics.first(
            @list.List([
              solve(
                seq([
                  @tactics.x_gen_tac(tm("(i : Num)")),
                  @tactics.repeat_tac(@tactics.gen_tac),
                  @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                  free_have("(i : Num) == 0", @int.asm_arith_tac),
                  subst_only("i"),
                  @tactics.rule_assum_tac(
                    @simp.rewrite_rule(ths([@lists.el(), @lists.hd()])),
                  ),
                  @simp.rewrite_tac(ths([@lists.el(), @lists.hd()])),
                  @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                  @tactics.exists_tac(tm("(L : " + sa + ")")),
                  startup_meson(ths([])),
                ]),
              ),
              solve(
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                  @tactics.exists_tac(tm("(Q : " + sa + ")")),
                  startup_meson(ths([])),
                ]),
              ),
              solve(
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                  @tactics.exists_tac(tm("(rp : " + sa + ")")),
                  startup_meson(ths([])),
                ]),
              ),
              solve(
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                  @tactics.exists_tac(tm("(A : " + sa + ")")),
                  startup_meson(ths([])),
                ]),
              ),
              seq([
                free_have(
                  keep("P") + "((s : Wstore),(f : Wframe),(vs : List[Value]))",
                  seq([
                    @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                    @tactics.exists_tac(tm("(P2 : " + sa + ")")),
                    startup_meson(ths([])),
                  ]),
                ),
                startup_meson(ths([])),
              ]),
            ]),
          ),
        ])(g)
      },
    ]),
  )
}
