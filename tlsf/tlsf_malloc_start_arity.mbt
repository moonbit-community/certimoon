///|
fn prove_tlsf_start_keep_arity() -> Unit raise {
  let sa = sassn
  let _ = startup_lemma(
    "tlsf_start_keep_result_arity",
    startup_quant() +
    "∀ P : " +
    sa +
    ", ∀ fr : " +
    hprop +
    ", ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ m : Num, (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", P(vs,lc,gs,ms,h) → LENGTH(vs) == m) && keep(" +
    startup_env() +
    ",lift(P,fr),s,f,vs) → LENGTH(vs) == m",
    seq([
      @simp.rewrite_tac(ths([thm("keep"), thm("lift")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_assum(th => {
        @tactics.strip_assume_tac(@drule.match_mp(thm("star_some"))(th))
      }),
      startup_meson(ths([])),
    ]),
  )
}
