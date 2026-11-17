// Ordinary releases keep the page in its existing partial-page list.

///|
fn prove_tlsf_block_free_lists() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let v = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}, ∀ b : \{w}"
  let u = "tlsf_small_used((cached : \{ls})((p : \{w})),(live : \{ls})(p))"
  let un = "tlsf_small_used((cached : \{ls})((p : \{w})),tlsf_small_remove((b : \{w}),(live : \{ls})(p)))"
  let args = "(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw})"
  let narg = "ps,sz,tlsf_block_free_loc(loc,(p : \{w}),(b : \{w})),cached,tlsf_block_free_live(live,p,b),fast,partial"
  let _ = lemma(
    "tlsf_small_lists_release_partial",
    "\{v}, tlsf_small_lists_ok(\{args}) && MEM(p,ps) && 1 < \{u} && \{u} < tlsf_small_total(sz(p)) && \{u} == SUC(\{un}) → tlsf_small_lists_ok(\{narg})",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "0 < \{un} && \{un} < tlsf_small_total((sz : (\{w}) -> Num)((p : \{w})))",
          @int.asm_arith_tac,
        ),
        @tactics.undisch_tac(tm("tlsf_small_lists_ok(" + args + ")")),
        rw([thm("tlsf_small_lists_ok")]),
        strip,
        rw([
          thm("tlsf_small_lists_ok"),
          thm("tlsf_block_free_loc"),
          thm("tlsf_block_free_live"),
          thm("tlsf_small_put"),
        ]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                @tactics.disch_tac,
                @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
                subst_vars(),
                arw([]),
                small_meson(ths([])),
              ]),
            ),
            solve(small_meson(ths([]))),
            solve(
              seq([
                @tactics.x_gen_tac(tm("(j : Num)")),
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                @tactics.disch_tac,
                @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
                subst_vars(),
                arw([]),
                small_meson(ths([])),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let cls = "DIV((sz : (\{w}) -> Num)((p : \{w})),8)"
  let nfull = "ps,sz,tlsf_block_free_loc(loc,(p : \{w}),(b : \{w})),cached,tlsf_block_free_live(live,p,b),fast,tlsf_small_put_class(partial,\{cls},CONS(p,partial(\{cls})))"
  let _ = lemma(
    "tlsf_small_lists_release_full",
    "\{v}, tlsf_small_lists_ok(\{args}) && MEM(p,ps) && 8 <= sz(p) && sz(p) <= 256 && MOD(sz(p),8) == 0 && \{u} == tlsf_small_total(sz(p)) && \{u} == SUC(\{un}) → tlsf_small_lists_ok(\{nfull})",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_small_class_bounds"), [
            "(sz : (" + w + ") -> Num)((p : " + w + "))",
          ]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_small_capacity"), [
            "(sz : (" + w + ") -> Num)((p : " + w + "))",
          ]),
        ),
        arw([]),
        strip,
        free_have(
          "0 < \{un} && \{un} < tlsf_small_total((sz : (\{w}) -> Num)((p : \{w}))) && !(\{u} < tlsf_small_total(sz(p)))",
          @int.asm_arith_tac,
        ),
        @tactics.undisch_tac(tm("tlsf_small_lists_ok(" + args + ")")),
        rw([thm("tlsf_small_lists_ok")]),
        strip,
        free_have(
          "∀ j : Num, j < 33 → !MEM((p : \{w}),(partial : (Num) -> \{lw})(j))",
          small_meson(ths([])),
        ),
        free_have(
          "tlsf_count((p : \{w}),(partial : (Num) -> \{lw})(\{cls})) == 0",
          seq([rw([thm("tlsf_count_zero")]), small_meson(ths([]))]),
        ),
        rw([
          thm("tlsf_small_lists_ok"),
          thm("tlsf_block_free_loc"),
          thm("tlsf_block_free_live"),
          thm("tlsf_small_put"),
          thm("tlsf_small_put_class"),
        ]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                @tactics.disch_tac,
                @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
                subst_vars(),
                arw([thm("tlsf_small_count_cons"), @arith.add_clauses()]),
                @tactics.first(
                  @list.List([
                    solve(small_meson(ths([]))),
                    solve(
                      seq([
                        free_have(
                          "!((p : \{w}) == (q : \{w}))",
                          small_meson(ths([])),
                        ),
                        @class.cond_cases_tac,
                        arw([thm("tlsf_small_count_cons"), @arith.add_clauses()]),
                        small_meson(ths([])),
                      ]),
                    ),
                  ]),
                ),
              ]),
            ),
            solve(small_meson(ths([]))),
            solve(
              seq([
                @tactics.x_gen_tac(tm("(j : Num)")),
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                @class.cond_cases_tac,
                arw([@lists.mem()]),
                strip,
                @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
                subst_vars(),
                arw([]),
                small_meson(ths([])),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
