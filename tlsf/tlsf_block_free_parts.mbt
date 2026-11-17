// Exact control-flow equations for composing the shipped inlined branch.

///|
fn prove_tlsf_block_free_parts() -> Unit raise {
  let w = w32
  let calc = @wasm.compute_conv(
    [
      "tlsf_block_free_code", "tlsf_block_free_release", "tlsf_block_free_classify",
      "tlsf_block_free_publish", "tlsf_block_free_last_test", "tlsf_block_free_reclaim",
      "tlsf_block_free_unlink",
    ].map(thm),
  )
  let _ = lemma(
    "tlsf_block_free_parts",
    "∀ d : \{w}, ∀ free_idx : Num, tlsf_block_free_code(d,free_idx) == APPEND(tlsf_block_free_release(d,free_idx),APPEND(tlsf_block_free_classify(d,free_idx),[If(Tbv(SOME(T_num(T_i32))),tlsf_block_free_publish(d,free_idx),APPEND(tlsf_block_free_last_test(d,free_idx),[If(Tbv(SOME(T_num(T_i32))),tlsf_block_free_reclaim(d,free_idx),[EConstNum(ConstInt32((word(0) : \{w})))])]))]))",
    () => seq([@tactics.repeat_tac(@tactics.gen_tac), @tactics.conv_tac(calc)]),
  )
  let _ = lemma(
    "tlsf_block_free_reclaim_parts",
    "∀ d : \{w}, ∀ free_idx : Num, tlsf_block_free_reclaim(d,free_idx) == APPEND(tlsf_block_free_unlink(d,free_idx),[Local_get(0),Call(free_idx)])",
    () => seq([@tactics.repeat_tac(@tactics.gen_tac), @tactics.conv_tac(calc)]),
  )
}
