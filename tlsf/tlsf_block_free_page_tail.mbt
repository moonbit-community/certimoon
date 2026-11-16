// Separate the read-only page size word from the rest of the page heap.

///|
fn define_tlsf_block_free_page_tail() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let args = [
    "(p : " + w + ")",
    "(cap : Num)",
    "(s : Num)",
    "(loc : " + lw + ")",
    "(cached : " + lw + ")",
    "(live : " + lw + ")",
  ]
  let body = @equal.rhs(@kernel.concl(thm("tlsf_small_page_heap")))
  let tail = args_of(body, "star", 2).unwrap()[1]
  def(
    "tlsf_block_free_page_tail",
    "tlsf_block_free_page_tail(" + args.join(",") + ") == " + show(tail),
  )
  let pieces = small_star_parts(body)
  let without = Array::makei(pieces.length() - 1, j => {
    show(pieces[if j < 1 { j } else { j + 1 }])
  })
  def(
    "tlsf_block_free_page_without_total",
    "tlsf_block_free_page_without_total(" +
    args.join(",") +
    ") == " +
    small_star(without),
  )
}

///|
fn prove_tlsf_block_free_page_tail() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let _ = lemma(
    "tlsf_small_page_size_focus",
    "∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, tlsf_small_page_heap(p,cap,s,loc,cached,live) == star(pts(val(p)+8,serialise_i32((word(s) : \{w}))),tlsf_block_free_page_tail(p,cap,s,loc,cached,live))",
    @simp.rewrite_tac(
      ths([thm("tlsf_small_page_heap"), thm("tlsf_block_free_page_tail")]),
    ),
  )
  let _ = lemma(
    "tlsf_small_page_total_focus",
    "∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, tlsf_small_page_heap(p,cap,s,loc,cached,live) == star(pts(val(p)+12,serialise_i32((word(tlsf_small_total(s)) : \{w}))),tlsf_block_free_page_without_total(p,cap,s,loc,cached,live))",
    @simp.rewrite_tac(
      ths([
        thm("tlsf_small_page_heap"),
        thm("tlsf_block_free_page_without_total"),
        thm("star_assoc"),
        thm("star_comm"),
        thm("star_left_comm"),
        thm("star_emp_hl"),
        thm("star_emp_hr"),
      ]),
    ),
  )
}
