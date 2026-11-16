// Memory::free may coalesce or change the physical-chain order. Its retained
// used-header guarantee carries every remaining small-page model through it.

///|
fn prove_tlsf_block_free_transport() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ m : \{w}, ∀ xs2 : \{lw}, ∀ hd2 : \{ht}"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))"
  let retained = "∀ x : \{w}, MEM(x,(xs : \{lw})) && !(x == (m : \{w})) && tlsf_used((hd : \{ht})(x)) → MEM(x,(xs2 : \{lw})) && (hd2 : \{ht})(x) == hd(x)"
  let _ = lemma(
    "tlsf_small_free_retained_pages",
    "\{vars}, \{backing} && !MEM(m,ps) && (\{retained}) → (∀ p : \{w}, MEM(p,ps) → MEM(p,xs2) && hd2(p) == hd(p))",
    seq([
      gen,
      rw([thm("tlsf_small_backing")]),
      strip,
      gen,
      @tactics.disch_tac,
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_free_backing",
    "\{vars}, \{backing} && !MEM(m,ps) && (\{retained}) → tlsf_small_backing(xs2,hd2,ps,sz,loc,cached,live,lim)",
    seq([
      gen,
      strip,
      g => {
        @tactics.assume_tac(
          block_under(
            inst(thm("tlsf_small_free_retained_pages"), [
              "(xs : " + lw + ")",
              "(hd : " + ht + ")",
              "(ps : " + lw + ")",
              "(sz : (" + w + ") -> Num)",
              "(loc : " + ls + ")",
              "(cached : " + ls + ")",
              "(live : " + ls + ")",
              "(lim : Num)",
              "(m : " + w + ")",
              "(xs2 : " + lw + ")",
              "(hd2 : " + ht + ")",
            ]),
            g,
          ),
        )(g)
      },
      @tactics.undisch_tac(tm(backing)),
      rw([thm("tlsf_small_backing")]),
      strip,
      gen,
      @tactics.disch_tac,
      free_have(
        "MEM((p : \{w}),(xs2 : \{lw})) && (hd2 : \{ht})(p) == (hd : \{ht})(p)",
        small_meson(ths([])),
      ),
      arw([]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_free_heap",
    "\{vars}, ∀ d : \{w}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, \{backing} && !MEM(m,ps) && (\{retained}) → tlsf_small(d,hd,ps,sz,loc,cached,live,fast,partial) == tlsf_small(d,hd2,ps,sz,loc,cached,live,fast,partial)",
    seq([
      gen,
      strip,
      g => {
        @tactics.assume_tac(
          block_under(
            inst(thm("tlsf_small_free_retained_pages"), [
              "(xs : " + lw + ")",
              "(hd : " + ht + ")",
              "(ps : " + lw + ")",
              "(sz : (" + w + ") -> Num)",
              "(loc : " + ls + ")",
              "(cached : " + ls + ")",
              "(live : " + ls + ")",
              "(lim : Num)",
              "(m : " + w + ")",
              "(xs2 : " + lw + ")",
              "(hd2 : " + ht + ")",
            ]),
            g,
          ),
        )(g)
      },
      @tactics.match_mp_tac(thm("tlsf_small_transport")),
      gen,
      @tactics.disch_tac,
      free_have(
        "(hd2 : \{ht})((p : \{w})) == (hd : \{ht})(p)",
        small_meson(ths([])),
      ),
      arw([]),
    ]),
  )
}
