// The initialization-prefix predicate refines the ordinary small-page
// slot/header and free-list predicates, in the compiler's reverse order.

///|
fn prove_tlsf_page_allocate_lists() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_allocate_list_head",
    "∀ n : Num, ∀ p : \{w}, ∀ s : Num, tlsf_small_head(REVERSE(tlsf_small_slots(p,s,n))) == tlsf_page_allocate_head(p,s,n)",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_small_slots"),
        @lists.reverse(),
        @lists.reverse_append(),
        @lists.append(),
        thm("tlsf_small_head"),
        thm("tlsf_page_allocate_head_suc"),
        thm("tlsf_page_allocate_head"),
        @lists.not_cons_nil(),
        @lists.hd(),
      ]),
    ]),
  )
  let _ = lemma(
    "tlsf_page_allocate_slots_refine",
    "∀ n : Num, ∀ p : \{w}, ∀ s : Num, tlsf_istar(tlsf_page_allocate_slot(p,s),n) == star(tlsf_istar(tlsf_small_slot_heap(p,s,(NIL : List[\{w}])),n),tlsf_small_links(REVERSE(tlsf_small_slots(p,s,n))))",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_istar"),
        thm("tlsf_small_slots"),
        @lists.reverse(),
        @lists.reverse_append(),
        @lists.append(),
        thm("tlsf_small_links"),
        thm("star_emp_hl"),
        thm("star_emp_hr"),
      ]),
      gen,
      arw([
        thm("tlsf_page_allocate_slot"),
        thm("tlsf_small_slot_heap"),
        @lists.mem(),
        thm("tlsf_page_allocate_list_head"),
        thm("star_assoc"),
        thm("star_comm"),
        thm("star_left_comm"),
        thm("star_emp_hr"),
        thm("star_emp_hl"),
      ]),
    ]),
  )
}
