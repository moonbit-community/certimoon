// All side conditions on the compiled small-page metadata follow from the
// combined invariant, rather than from assumptions about list contents.

///|
fn prove_tlsf_block_free_global_facts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))"
  let lists = "tlsf_small_lists_ok((ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw}))"
  let page = "tlsf_small_page_ok((lim : Num),(p : \{w}),val(tlsf_size((hd : \{ht})(p))),(sz : (\{w}) -> Num)(p),(loc : \{ls})(p),(cached : \{ls})(p),(live : \{ls})(p))"
  let _ = lemma(
    "tlsf_small_page_member_geometry",
    "\{vars}, ∀ p : \{w}, \{backing} && MEM(p,ps) → \{page} && !(p == word(0)) && val(p)+32 <= 4294967296 && 8 <= sz(p) && sz(p) <= 256 && MOD(sz(p),8) == 0 && DIV(sz(p),8) < 33",
    seq([
      gen,
      rw([thm("tlsf_small_backing")]),
      strip,
      free_have(page, small_meson(ths([]))),
      @tactics.undisch_tac(tm(page)),
      rw([thm("tlsf_small_page_ok")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_small_class_bounds"), [
          "(sz : (" + w + ") -> Num)((p : " + w + "))",
        ]),
      ),
      arw([]),
      strip,
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_partial_geometry",
    "\{vars}, \{backing} && \{lists} → (∀ j : Num, ∀ q : \{w}, j < 33 && MEM(q,partial(j)) → !(q == word(0)) && val(q)+32 <= 4294967296)",
    seq([
      gen,
      strip,
      @tactics.undisch_tac(tm(lists)),
      rw([thm("tlsf_small_lists_ok")]),
      strip,
      gen,
      strip,
      free_have("MEM((q : \{w}),(ps : \{lw}))", small_meson(ths([]))),
      @tactics.mp_tac(
        inst(thm("tlsf_small_page_member_geometry"), [
          "(xs : " + lw + ")",
          "(hd : " + ht + ")",
          "(ps : " + lw + ")",
          "(sz : (" + w + ") -> Num)",
          "(loc : " + ls + ")",
          "(cached : " + ls + ")",
          "(live : " + ls + ")",
          "(lim : Num)",
          "(fast : (Num) -> " + lw + ")",
          "(partial : (Num) -> " + lw + ")",
          "(q : " + w + ")",
        ]),
      ),
      arw([]),
      small_meson(ths([])),
    ]),
  )
  let u = "tlsf_small_used((cached : \{ls})((p : \{w})),(live : \{ls})(p))"
  let un = "tlsf_small_used((cached : \{ls})((p : \{w})),tlsf_small_remove((b : \{w}),(live : \{ls})(p)))"
  let part = "tlsf_small_partition((p : \{w}),(sz : (\{w}) -> Num)(p),(loc : \{ls})(p),(cached : \{ls})(p),(live : \{ls})(p))"
  let _ = lemma(
    "tlsf_small_live_release_usage",
    "\{vars}, ∀ p : \{w}, ∀ b : \{w}, \{backing} && MEM(p,ps) && MEM(b,live(p)) → 1 <= \{u} && \{u} <= tlsf_small_total(sz(p)) && tlsf_small_total(sz(p)) <= 66 && \{u} == SUC(\{un}) && (\{u} == 1 → cached(p) == NIL && tlsf_small_remove(b,live(p)) == NIL)",
    seq([
      gen,
      strip,
      free_have(
        "\{page} && \{part} && 8 <= (sz : (\{w}) -> Num)((p : \{w})) && (sz : (\{w}) -> Num)(p) <= 256",
        seq([
          @tactics.undisch_tac(tm(backing)),
          rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_small_release_model"), [
              "(p : " + w + ")",
              "(sz : (" + w + ") -> Num)((p : " + w + "))",
              "(b : " + w + ")",
              "(loc : " + ls + ")((p : " + w + "))",
              "(cached : " + ls + ")((p : " + w + "))",
              "(live : " + ls + ")((p : " + w + "))",
            ]),
            g,
          ),
        )(g)
      },
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_small_accounting"), [
              "(p : " + w + ")",
              "(sz : (" + w + ") -> Num)((p : " + w + "))",
              "(loc : " + ls + ")((p : " + w + "))",
              "(cached : " + ls + ")((p : " + w + "))",
              "(live : " + ls + ")((p : " + w + "))",
            ]),
            g,
          ),
        )(g)
      },
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_small_capacity"), [
              "(sz : (" + w + ") -> Num)((p : " + w + "))",
            ]),
            g,
          ),
        )(g)
      },
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              @tactics.disch_tac,
              free_have("\{un} == 0", @int.asm_arith_tac),
              @tactics.mp_tac(
                inst(thm("tlsf_small_reclaimable"), [
                  "(cached : " + ls + ")((p : " + w + "))",
                  "tlsf_small_remove((b : " +
                  w +
                  "),(live : " +
                  ls +
                  ")((p : " +
                  w +
                  ")))",
                ]),
              ),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
