// Derive the slot index and table bounds from the allocator invariant.

///|
fn prove_tlsf_block_free_entry() -> Unit raise {
  let w = w32
  let args = block_model_args()
  let model = page_model_variables()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_small_live_slot",
    page_quantify(model + [("p", w), ("b", w)]) +
    block_backing(args) +
    " && MEM(" +
    p +
    "," +
    args[8] +
    ") && MEM(" +
    b +
    "," +
    args[12] +
    "(" +
    p +
    ")) → (∃ i : Num, i < " +
    block_total(args, p) +
    " && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    args[9] +
    "(" +
    p +
    "),i))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          "tlsf_small_partition(" +
          p +
          "," +
          args[9] +
          "(" +
          p +
          ")," +
          args[10] +
          "(" +
          p +
          ")," +
          args[11] +
          "(" +
          p +
          ")," +
          args[12] +
          "(" +
          p +
          "))",
          seq([
            @tactics.undisch_tac(tm(block_backing(args))),
            rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
            small_meson(ths([])),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_small_live_unique"), [
            p,
            args[9] + "(" + p + ")",
            b,
            args[10] + "(" + p + ")",
            args[11] + "(" + p + ")",
            args[12] + "(" + p + ")",
          ]),
        ),
        arw([thm("tlsf_small_slots_member")]),
        small_meson(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_block_free_large_bound",
    page_quantify(model) +
    "∀ client : " +
    hprop +
    ", ∀ h : " +
    heap +
    ", star(" +
    block_large(args) +
    ",client,h) → val(" +
    args[0] +
    ") <= 4294965088",
    () => {
      seq([
        rw([
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("tlsf_physical_ok"),
          thm("star"),
        ]),
        small_meson(ths([])),
      ])
    },
  )
}
