// Focus one backing page and carry all other page heaps through functional
// updates of the local and live maps.

///|
fn prove_tlsf_block_free_pages() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let args = "(ps : \{lw}),(hd : \{ht}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls})"
  let vs = "∀ ps : \{lw}, ∀ hd : \{ht}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}"
  let page = "(p : \{w}) => tlsf_small_page_heap(p,val(tlsf_size((hd : \{ht})(p))),(sz : (\{w}) -> Num)(p),(loc : \{ls})(p),(cached : \{ls})(p),(live : \{ls})(p))"
  let hlist = lemma(
    "tlsf_small_pages_hlist",
    "\{vs}, tlsf_small_pages_heap(\{args}) == tlsf_small_hlist((\{page}),ps)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_small_pages_heap"), thm("tlsf_small_hlist")]),
        gen,
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_pages_focus",
    "\{vs}, ∀ p : \{w}, tlsf_count(p,ps) == 1 → tlsf_small_pages_heap(\{args}) == star(tlsf_small_page_heap(p,val(tlsf_size(hd(p))),sz(p),loc(p),cached(p),live(p)),tlsf_small_pages_heap(tlsf_small_remove(p,ps),hd,sz,loc,cached,live))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([hlist]),
        @tactics.match_mp_tac(thm("tlsf_small_hlist_focus")),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_pages_release_rest",
    "\{vs}, ∀ p : \{w}, ∀ b : \{w}, tlsf_small_pages_heap(tlsf_small_remove(p,ps),hd,sz,tlsf_block_free_loc(loc,p,b),cached,tlsf_block_free_live(live,p,b)) == tlsf_small_pages_heap(tlsf_small_remove(p,ps),hd,sz,loc,cached,live)",
    () => {
      seq([
        gen,
        rw([hlist]),
        @tactics.match_mp_tac(thm("tlsf_small_hlist_cong")),
        gen,
        rw([
          thm("tlsf_small_remove_member"),
          thm("tlsf_block_free_loc"),
          thm("tlsf_block_free_live"),
          thm("tlsf_small_put"),
        ]),
        strip,
        arw([]),
      ])
    },
  )
}
