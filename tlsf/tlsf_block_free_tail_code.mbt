// These definitions assemble already-transcribed fragments; the equality
// back to the shipped 167-instruction branch is checked in the kernel.

///|
fn define_tlsf_block_free_tail_code() -> Unit raise {
  let w = w32
  def(
    "tlsf_block_free_else",
    "tlsf_block_free_else((d : \{w}),(free_idx : Num)) == APPEND(tlsf_block_free_last_test(d,free_idx),[If(Tbv(SOME(T_num(T_i32))),tlsf_block_free_reclaim(d,free_idx),[EConstNum(ConstInt32((word(0) : \{w})))])])",
  )
  def(
    "tlsf_block_free_tail",
    "tlsf_block_free_tail((d : \{w}),(free_idx : Num)) == APPEND(tlsf_block_free_classify(d,free_idx),[If(Tbv(SOME(T_num(T_i32))),tlsf_block_free_publish(d,free_idx),tlsf_block_free_else(d,free_idx))])",
  )
}

///|
fn prove_tlsf_block_free_tail_code() -> Unit raise {
  let w = w32
  let _ = lemma(
    "tlsf_block_free_tail_parts",
    "∀ d : \{w}, ∀ free_idx : Num, tlsf_block_free_code(d,free_idx) == APPEND(tlsf_block_free_release(d,free_idx),tlsf_block_free_tail(d,free_idx))",
    () => {
      @simp.rewrite_tac(
        ths([
          thm("tlsf_block_free_parts"),
          thm("tlsf_block_free_tail"),
          thm("tlsf_block_free_else"),
        ]),
      )
    },
  )
  ignore(
    sym_prove(
      "tlsf_block_free_zero",
      "∀ lc : List[Value], ∀ R : \{rty}, sl_triple(st(NIL,lc,R),[EConstNum(ConstInt32((word(0) : \{w})))],st([V_num(ConstInt32((word(0) : \{w})))],lc,R))",
      [],
      () => [],
      kind="lemma",
    ),
  )
}
