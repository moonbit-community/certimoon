// Pages occupy different used physical memories. Their complete backing
// intervals are disjoint, independently of their free-list order.

///|
fn prove_tlsf_small_page_separation() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let rel = "(m : \{w}) => (n : \{w}) => val(m)+8+val(tlsf_size((hd : \{ht})(m))) <= val(n)"
  let _ = lemma(
    "tlsf_small_pairwise_separate",
    "∀ xs : \{lw}, ∀ R : (\{w}) -> (\{w}) -> Bool, ∀ p : \{w}, ∀ q : \{w}, PAIRWISE(R,xs) && MEM(p,xs) && MEM(q,xs) && !(p == q) → R(p,q) || R(q,p)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([@lists.pairwise(), @lists.mem(), @equal.gsym(@lists.all_mem())]),
        gen,
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        small_meson(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_backing_separate",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ prev : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ p : \{w}, ∀ q : \{w}, tlsf_layout(prev,a,lim,top,xs,hd) && tlsf_small_backing(xs,hd,ps,sz,loc,cached,live,lim) && MEM(p,ps) && MEM(q,ps) && !(p == q) → val(p)+8+val(tlsf_size(hd(p))) <= val(q) || val(q)+8+val(tlsf_size(hd(q))) <= val(p)",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "MEM((p : \{w}),(xs : \{lw})) && MEM((q : \{w}),xs)",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))",
              ),
            ),
            rw([thm("tlsf_small_backing")]),
            small_meson(ths([])),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_layout_order"), [
            "(xs : \{lw})",
            "(prev : \{w})",
            "(a : Num)",
            "(lim : Num)",
            "(top : \{w})",
            "(hd : \{ht})",
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_small_pairwise_separate"), [
            "(xs : \{lw})",
            rel,
            "(p : \{w})",
            "(q : \{w})",
          ]),
        ),
        arw([]),
      ])
    },
  )
}
