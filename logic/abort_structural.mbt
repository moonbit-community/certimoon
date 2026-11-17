// Structural rules used to compose the normal and trapping allocation paths.

///|
fn prove_abort_structural() -> Unit raise {
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, "
  let tr = (p : String) => {
    "sl_abort_m(" +
    env +
    "," +
    p +
    ",(bs : List[B_e]),(Q : " +
    sassn +
    "),(A : " +
    sassn +
    "))"
  }
  let _ = lemma(
    "sl_abort_ex_m",
    vars +
    "∀ pp : (X,List[Value],List[Value],List[Value],Num," +
    heap +
    ") -> Bool, ∀ bs : List[B_e], ∀ Q : " +
    sassn +
    ", ∀ A : " +
    sassn +
    ", (∀ x : X, " +
    tr("pp(x)") +
    ") → " +
    tr(
      "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => ∃ x : X, pp(x,vs,lc,gs,ms,h)",
    ),
    seq([
      @simp.rewrite_tac(ths([thm("sl_abort_m"), thm("keep"), thm("lift_ex")])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_abort_pure_m",
    vars +
    "∀ c : Bool, ∀ p : " +
    sassn +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sassn +
    ", ∀ A : " +
    sassn +
    ", (c → " +
    tr("p") +
    ") → " +
    tr(
      "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => c && p(vs,lc,gs,ms,h)",
    ),
    seq([
      @simp.rewrite_tac(ths([thm("sl_abort_m"), thm("keep"), thm("lift_pure")])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_abort_false_m",
    vars +
    "∀ bs : List[B_e], ∀ Q : " +
    sassn +
    ", ∀ A : " +
    sassn +
    ", " +
    tr(sa_false),
    @simp.rewrite_tac(
      ths([thm("sl_abort_m"), thm("keep"), thm("lift"), thm("star")]),
    ),
  )
  let _ = lemma(
    "sl_abort_pre_m",
    vars +
    "∀ p : " +
    sassn +
    ", ∀ p2 : " +
    sassn +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sassn +
    ", ∀ A : " +
    sassn +
    ", (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", p2(vs,lc,gs,ms,h) → p(vs,lc,gs,ms,h)) && " +
    tr("p") +
    " → " +
    tr("p2"),
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("sl_abort_conseq_m")),
      @tactics.exists_tac(tm("(p : " + sassn + ")")),
      @tactics.exists_tac(tm("(Q : " + sassn + ")")),
      @tactics.exists_tac(tm("(A : " + sassn + ")")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}
