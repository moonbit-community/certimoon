// Only the 33 concrete table classes matter to a well-sized page model.

///|
fn prove_tlsf_block_free_lists_ext() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ fast : (Num) -> \{lw}, ∀ part1 : (Num) -> \{lw}, ∀ part2 : (Num) -> \{lw}"
  let args = "(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw})"
  let _ = lemma(
    "tlsf_small_lists_partial_ext",
    "\{vars}, (∀ p : \{w}, MEM(p,ps) → DIV(sz(p),8) < 33) && (∀ j : Num, j < 33 → part1(j) == part2(j)) → (tlsf_small_lists_ok(\{args},part1) == tlsf_small_lists_ok(\{args},part2))",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_small_lists_ok")]),
        @tactics.eq_tac,
        strip,
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.x_gen_tac(tm("(q : " + w + ")")),
              @tactics.disch_tac,
              free_have(
                "(part1 : (Num) -> \{lw})(DIV((sz : (\{w}) -> Num)((q : \{w})),8)) == (part2 : (Num) -> \{lw})(DIV(sz(q),8))",
                small_meson(ths([])),
              ),
              small_meson(ths([])),
            ]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                small_meson(ths([])),
                seq([
                  @tactics.x_gen_tac(tm("(j : Num)")),
                  @tactics.x_gen_tac(tm("(q : " + w + ")")),
                  strip,
                  free_have(
                    "(part1 : (Num) -> \{lw})((j : Num)) == (part2 : (Num) -> \{lw})(j)",
                    small_meson(ths([])),
                  ),
                  small_meson(ths([])),
                ]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_table_partial_ext",
    "∀ d : \{w}, ∀ fast : (Num) -> \{lw}, ∀ part1 : (Num) -> \{lw}, ∀ part2 : (Num) -> \{lw}, (∀ j : Num, j < 33 → part1(j) == part2(j)) → tlsf_small_table(d,fast,part1) == tlsf_small_table(d,fast,part2)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_small_table")]),
        @tactics.match_mp_tac(thm("tlsf_istar_cong")),
        gen,
        @tactics.disch_tac,
        free_have(
          "(part1 : (Num) -> \{lw})((i : Num)) == (part2 : (Num) -> \{lw})(i)",
          small_meson(ths([])),
        ),
        rw([thm("tlsf_small_table_item")]),
        arw([]),
      ])
    },
  )
}
