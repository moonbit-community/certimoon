// Removing the returned slot from the live model changes only that slot's
// ownership. All other slot headers and omitted client payloads stay equal.

///|
fn prove_tlsf_block_free_slots() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let v = "∀ n : Num, ∀ p : \{w}, ∀ s : Num, ∀ live : \{lw}, ∀ b : \{w}, ∀ i : Num"
  let old = "tlsf_small_slot_heap((p : \{w}),(s : Num),(live : \{lw}))"
  let new = "tlsf_small_slot_heap((p : \{w}),(s : Num),tlsf_small_remove((b : \{w}),(live : \{lw})))"
  let rest = (ff : String) => {
    "tlsf_istar((j : Num) => if j == (i : Num) { emp } else { \{ff}(j) },(n : Num))"
  }
  let _ = lemma(
    "tlsf_small_release_slots_frame",
    "\{v}, (∀ j : Num, j < n && !(j == i) → !(tlsf_small_slot(p,s,j) == b)) → \{rest(new)} == \{rest(old)}",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(thm("tlsf_istar_cong")),
        @tactics.x_gen_tac(tm("(j : Num)")),
        @tactics.disch_tac,
        @class.asm_cases_tac(tm("(j : Num) == (i : Num)")),
        arw([]),
        free_have(
          "!(tlsf_small_slot((p : \{w}),(s : Num),(j : Num)) == (b : \{w}))",
          small_meson(ths([])),
        ),
        rw([thm("tlsf_small_slot_heap"), thm("tlsf_small_remove_member")]),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_release_slots_focus",
    "\{v}, i < n && (∀ j : Num, j < n && !(j == i) → !(tlsf_small_slot(p,s,j) == b)) → tlsf_istar(\{new},n) == star(\{new}(i),\{rest(old)})",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_istar_focus"), ["(n : Num)", new, "(i : Num)"]),
        ),
        arw([]),
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_small_release_slots_frame"), [
            "(n : Num)",
            "(p : " + w + ")",
            "(s : Num)",
            "(live : " + lw + ")",
            "(b : " + w + ")",
            "(i : Num)",
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        arw([]),
      ])
    },
  )
}
