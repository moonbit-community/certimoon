// List links occupy the first four bytes of free payloads. Reclamation may
// forget their pointer values, but retains ownership of those exact bytes.

///|
fn prove_tlsf_block_free_recover_links() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ff = "(b : \{w}) => tlsf_bytes(val(b)+8,4)"
  let _ = lemma(
    "tlsf_small_links_bytes",
    "∀ xs : \{lw}, ∀ h : \{heap}, tlsf_small_links(xs,h) → tlsf_small_hlist((\{ff}),xs,h)",
    () => {
      @tactics.thenl(
        @lists.list_induct_tac,
        @list.List([
          rw([thm("tlsf_small_links"), thm("tlsf_small_hlist")]),
          seq([
            rw([thm("tlsf_small_links"), thm("tlsf_small_hlist")]),
            gen,
            @tactics.disch_tac,
            @tactics.match_mp_tac(
              inst(thm("star_mono"), [
                "pts(val((h : " +
                w +
                "))+8,serialise_i32(tlsf_small_head((t : " +
                lw +
                "))))",
                "tlsf_bytes(val((h : " + w + "))+8,4)",
                "tlsf_small_links((t : " + lw + "))",
                "tlsf_small_hlist((" + ff + "),(t : " + lw + "))",
                "(h' : " + heap + ")",
              ]),
            ),
            arw([]),
            rw([thm("tlsf_bytes_word")]),
            gen,
            @tactics.disch_tac,
            @tactics.exists_tac(tm("tlsf_small_head((t : " + lw + "))")),
            arw([]),
          ]),
        ]),
      )
    },
  )
}
