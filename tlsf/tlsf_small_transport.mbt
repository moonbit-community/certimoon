// Large-allocator calls frame the small heap. The only model facts to carry
// across them are that every existing page stays used with the same capacity;
// physical-chain insertion and changes to the last flag are permitted.

///|
fn prove_tlsf_small_transport() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let modelvars = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}"
  let agree = "∀ p : \{w}, MEM(p,(ps : \{lw})) → tlsf_size((hd2 : \{ht})(p)) == tlsf_size((hd : \{ht})(p))"
  let _ = lemma(
    "tlsf_small_pages_transport",
    "∀ ps : \{lw}, ∀ hd : \{ht}, ∀ hd2 : \{ht}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, (\{agree}) → tlsf_small_pages_heap(ps,hd,sz,loc,cached,live) == tlsf_small_pages_heap(ps,hd2,sz,loc,cached,live)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_small_pages_heap"), @lists.mem()]),
        gen,
        strip,
        free_have(
          "tlsf_size((hd2 : \{ht})((h : \{w}))) == tlsf_size((hd : \{ht})(h))",
          small_meson(ths([])),
        ),
        arw([]),
        @tactics.ap_term_tac,
        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
        small_meson(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_transport",
    "∀ d : \{w}, \{modelvars}, ∀ hd : \{ht}, ∀ hd2 : \{ht}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, (\{agree}) → tlsf_small(d,hd,ps,sz,loc,cached,live,fast,partial) == tlsf_small(d,hd2,ps,sz,loc,cached,live,fast,partial)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_small_pages_transport"), [
            "(ps : \{lw})",
            "(hd : \{ht})",
            "(hd2 : \{ht})",
            "(sz : (\{w}) -> Num)",
            "(loc : \{ls})",
            "(cached : \{ls})",
            "(live : \{ls})",
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        rw([thm("tlsf_small")]),
        arw([]),
      ])
    },
  )
  let retained = "∀ p : \{w}, MEM(p,(ps : \{lw})) → MEM(p,(xs2 : \{lw})) && tlsf_used((hd2 : \{ht})(p)) && tlsf_size(hd2(p)) == tlsf_size((hd : \{ht})(p))"
  let _ = lemma(
    "tlsf_small_backing_transport",
    "∀ xs : \{lw}, ∀ hd : \{ht}, \{modelvars}, ∀ lim : Num, ∀ xs2 : \{lw}, ∀ hd2 : \{ht}, ∀ lim2 : Num, tlsf_small_backing(xs,hd,ps,sz,loc,cached,live,lim) && lim <= lim2 && lim2 <= 4294967296 && (\{retained}) → tlsf_small_backing(xs2,hd2,ps,sz,loc,cached,live,lim2)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_backing")]),
        strip,
        gen,
        @tactics.disch_tac,
        @tactics.first_x_assum(th => {
          @tactics.mp_tac(@bool.spec(tm("(p : \{w})"), th))
        }),
        arw([]),
        strip,
        @tactics.first_x_assum(th => {
          @tactics.mp_tac(@bool.spec(tm("(p : \{w})"), th))
        }),
        arw([]),
        rw([thm("tlsf_small_page_ok")]),
        @tactics.repeat_tac(@tactics.strip_tac),
        arw([]),
        @tactics.first(
          @list.List([solve(@int.asm_arith_tac), solve(small_meson(ths([])))]),
        ),
      ])
    },
  )
}
