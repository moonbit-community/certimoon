///|
fn prove_tlsf_split_module_ex() -> Unit raise {
  let sa = sassn
  let pp = "(A, List[Value], List[Value], List[Value], Num, \{heap}) -> Bool"
  let ex = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ x : A, (P : \{pp})(x, vs, lc, gs, ms, h))"
  let _ = lemma(
    "sl_ex_m",
    "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ P : \{pp}, ∀ code : List[B_e], ∀ Q : \{sa}, ∀ labels : List[\{sa}], (∀ x : A, sl_triple_m(fs, tabs, inst, P(x), code, Q, labels)) → sl_triple_m(fs, tabs, inst, \{ex}, code, Q, labels)",
    () => {
      seq([
        @simp.rewrite_tac(
          ths([thm("sl_triple_m"), thm("triple_l"), thm("keep"), thm("lift_ex")]),
        ),
        @meson.meson_tac(ths([])),
      ])
    },
  )
}
