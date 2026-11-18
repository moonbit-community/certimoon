///|
fn prove_tlsf_start_structural() -> Unit raise {
  let sa = sassn
  let env = startup_env()
  let quant = startup_quant()
  let ent = (p : String, q : String) => {
    "(∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", " +
    p +
    "(vs,lc,gs,ms,h) → " +
    q +
    "(vs,lc,gs,ms,h))"
  }
  let tr = (p : String, q : String, a : String) => {
    "tlsf_sl_abort_r(" +
    env +
    ",(rp : " +
    sa +
    ")," +
    p +
    ",(bs : List[B_e])," +
    q +
    ",(ls : List[" +
    sa +
    "])," +
    a +
    ")"
  }
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _ = startup_lemma(
    "tlsf_sl_abort_r_ex",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : (A) -> " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", (∀ x : A, " +
    tr("P(x)", "Q", "A") +
    ") → " +
    tr(
      "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => ∃ x : A, P(x,vs,lc,gs,ms,h)",
      "Q",
      "A",
    ),
    seq([
      rw([thm("tlsf_sl_abort_r"), thm("keep"), thm("lift_ex")]),
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_conseq",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ P2 : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ Q2 : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", ∀ A2 : " +
    sa +
    ", " +
    ent("P2", "P") +
    " && " +
    tr("P", "Q", "A") +
    " && " +
    ent("Q", "Q2") +
    " && " +
    ent("A", "A2") +
    " → " +
    tr("P2", "Q2", "A2"),
    seq([
      rw([thm("tlsf_sl_abort_r")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      g => {
        let a = args_of(g.1, "tlsf_safer_abort", 8).unwrap()
        let keep = (p : String) => {
          "keep(" +
          env +
          ",lift((" +
          p +
          " : " +
          sa +
          "),(fr : " +
          hprop +
          ")))"
        }
        let olda = "(s : Wstore) => (f : Wframe) => " + keep("A") + "(s,f,NIL)"
        let rule = inst(thm("tlsf_safer_abort_mono"), [
          show(a[0]),
          olda,
          show(a[7]),
          show(a[1]),
          show(a[2]),
          show(a[3]),
          keep("Q"),
          show(a[4]),
          show(a[5]),
          show(a[5]),
          show(a[6]),
          show(a[6]),
        ])
        return seq([
          @tactics.match_mp_tac(rule),
          @simp.rewrite_tac(ths([@lists.length_map()])),
          @tactics.repeat_tac(@tactics.conj_tac),
          @tactics.first(
            @list.List([
              solve(
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @simp.asm_rewrite_tac(ths([])),
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
              solve(
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.match_mp_tac(thm("abort_keep_lift_mono")),
                  @tactics.exists_tac(tm("(Q : " + sa + ")")),
                  startup_meson(ths([])),
                ]),
              ),
              seq([
                have(
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
