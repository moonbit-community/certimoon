///|
fn prove_tlsf_free_begin_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let nh = "tlsf_release((hd : \{ht}),(m : \{w}))"
  let marked = "tlsf_mark(\{nh},(m : \{w}))"
  let xs = "(xs : \{lw})"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht}))"
  let vars = "∀ xs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ bl : \{bt}"
  let raw = [thm("tlsf_release"), thm("tlsf_mark"), thm("tlsf_put")]
  let fields = [thm("tlsf_free_mark_fields"), thm("tlsf_free_release_fields")]
  let _ = lemma(
    "tlsf_free_begin_model",
    "\{vars}, \{old} && tlsf_used(hd(m)) && tlsf_bins_match(\{xs},hd,bl) → tlsf_free_geom(d,lim,top,\{xs},\{nh},m) && !tlsf_used((\{nh})(m)) && tlsf_size((\{nh})(m)) == tlsf_size(hd(m)) && tlsf_bins_match(\{xs},\{marked},bl) && (∀ x : \{w}, !(x == m) → (\{nh})(x) == hd(x))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "tlsf_layout((word(0) : \{w}),tlsf_origin((d : \{w})),(lim : Num),(top : \{w}),\{xs},(hd : \{ht})) == tlsf_layout(word(0),tlsf_origin(d),lim,top,xs,\{marked})",
          seq([
            @tactics.match_mp_tac(thm("tlsf_layout_fields")),
            gen,
            @tactics.disch_tac,
            rw(fields),
          ]),
        ),
        free_have(
          "tlsf_coalesced(\{xs},\{marked})",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_coalesced_mono"), [xs, "(hd : \{ht})", marked]),
            ),
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(
                  seq([
                    @tactics.undisch_tac(tm(old)),
                    rw([thm("tlsf_physical_ok")]),
                    @meson.meson_tac(ths([])),
                  ]),
                ),
                solve(
                  seq([gen, strip, rw(fields), @meson.asm_meson_tac(ths([]))]),
                ),
              ]),
            ),
          ]),
        ),
        free_have(
          "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{nh},(m : \{w}))",
          seq([
            @tactics.undisch_tac(tm(old)),
            rw([thm("tlsf_physical_ok"), thm("tlsf_free_geom")]),
            strip,
            arw([]),
            @meson.asm_meson_tac(ths([])),
          ]),
        ),
        free_have(
          "tlsf_bins_match(\{xs},\{marked},(bl : \{bt}))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_free_bins_transport"), [
                xs,
                xs,
                "(hd : \{ht})",
                marked,
                "(bl : \{bt})",
              ]),
            ),
            arw([]),
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(
                  seq([
                    gen,
                    @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")),
                    subst_vars(),
                    arw(fields),
                  ]),
                ),
                solve(
                  seq([
                    gen,
                    strip,
                    free_have(
                      "!((x : \{w}) == (m : \{w}))",
                      @meson.asm_meson_tac(ths([])),
                    ),
                    arw(raw),
                  ]),
                ),
              ]),
            ),
          ]),
        ),
        arw(fields),
        gen,
        @tactics.disch_tac,
        arw(raw),
      ])
    },
  )
}
