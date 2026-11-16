// Symbolic execution can close an unreachable ordinary continuation just as
// it closes one in an ambient call specification. This is vacuous safety,
// derived from the existing separation-logic definition.

///|
fn prove_false_labels() -> Unit raise {
  let _ = lemma(
    "sl_false_l",
    "∀ bs : List[B_e], ∀ q : \{sassn}, ∀ ls : List[\{sassn}], sl_triple_l(\{sa_false},bs,q,ls)",
    @simp.rewrite_tac(
      ths([thm("sl_triple_l"), thm("triple_l"), thm("lift"), thm("star")]),
    ),
  )
  ignore(
    sym_prove(
      "example_false_ordinary_continuation",
      "∀ q : \{sassn}, sl_triple(\{sa_false},[Unreachable],q)",
      [],
      [],
    ),
  )
}
