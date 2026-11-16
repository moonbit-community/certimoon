// Reclamation removes the page domain entry. Its otherwise-unused map
// values may retain the newly assembled local list without owning any heap.

///|
fn prove_tlsf_block_free_last_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}, ∀ b : \{w}"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))"
  let smallargs = [
    "(ps : " + lw + ")",
    "(sz : (" + w + ") -> Num)",
    "(loc : " + ls + ")",
    "(cached : " + ls + ")",
    "(live : " + ls + ")",
    "(fast : (Num) -> " + lw + ")",
    "(partial : (Num) -> " + lw + ")",
  ]
  let lists = "tlsf_small_lists_ok(" + smallargs.join(",") + ")"
  let pages = "tlsf_small_remove((p : \{w}),(ps : \{lw}))"
  let loc = "tlsf_block_free_loc((loc : \{ls}),(p : \{w}),(b : \{w}))"
  let live = "tlsf_block_free_live((live : \{ls}),(p : \{w}),(b : \{w}))"
  let _ = lemma(
    "tlsf_small_backing_remove_page",
    "\{vars}, \{backing} → tlsf_small_backing(xs,hd,\{pages},sz,\{loc},cached,\{live},lim)",
    seq([
      gen,
      rw([
        thm("tlsf_small_backing"),
        thm("tlsf_small_remove_member"),
        thm("tlsf_block_free_loc"),
        thm("tlsf_block_free_live"),
        thm("tlsf_small_put"),
      ]),
      strip,
      gen,
      strip,
      arw([]),
      small_meson(ths([])),
    ]),
  )
  let geometry = ["(xs : " + lw + ")", "(hd : " + ht + ")"] +
    smallargs[:5].to_owned() +
    ["(lim : Num)"] +
    smallargs[5:].to_owned()
  let k = "DIV((sz : (\{w}) -> Num)((p : \{w})),8)"
  let filter = "(j : Num) => tlsf_small_remove((p : \{w}),(partial : (Num) -> \{lw})(j))"
  let actual = "tlsf_small_put_class((partial : (Num) -> \{lw}),\{k},tlsf_small_remove((p : \{w}),partial(\{k})))"
  let newargs = [
    pages,
    "(sz : (" + w + ") -> Num)",
    loc,
    "(cached : " + ls + ")",
    live,
    "(fast : (Num) -> " + lw + ")",
  ]
  let _ = lemma(
    "tlsf_small_lists_release_last_class",
    "\{vars}, \{backing} && \{lists} && MEM(p,ps) && cached(p) == NIL → tlsf_small_lists_ok(\{newargs.join(",")},\{actual})",
    seq([
      gen,
      strip,
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(
              thm("tlsf_small_page_member_geometry"),
              geometry + ["(p : " + w + ")"],
            ),
            g,
          ),
        )(g)
      },
      free_have(
        "tlsf_small_lists_ok(\{newargs.join(",")},(\{filter}))",
        free_apply(
          inst(
            thm("tlsf_small_lists_remove_empty_page"),
            smallargs + ["(p : " + w + ")", "(b : " + w + ")"],
          ),
        ),
      ),
      g => {
        @tactics.assume_tac(
          block_under(
            inst(
              thm("tlsf_small_partial_remove_class"),
              smallargs + ["(p : " + w + ")", "(b : " + w + ")"],
            ),
            g,
          ),
        )(g)
      },
      free_have(
        "∀ j : Num, j < 33 → (\{filter})(j) == (\{actual})(j)",
        small_meson(ths([])),
      ),
      free_have(
        "∀ q : \{w}, MEM(q,\{pages}) → DIV((sz : (\{w}) -> Num)(q),8) < 33",
        seq([
          gen,
          rw([thm("tlsf_small_remove_member")]),
          strip,
          @tactics.mp_tac(
            inst(
              thm("tlsf_small_page_member_geometry"),
              geometry + ["(q : " + w + ")"],
            ),
          ),
          arw([]),
          small_meson(ths([])),
        ]),
      ),
      g => {
        @tactics.mp_tac(
          block_under(
            inst(
              thm("tlsf_small_lists_partial_ext"),
              newargs + [filter, actual],
            ),
            g,
          ),
        )(g)
      },
      arw([]),
    ]),
  )
}
