///|
fn prove_tlsf_split_interior() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_layout_interior",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, ∀ r : \{w}, tlsf_layout(p, a, lim, top, xs, hd) && MEM(m, xs) && val(m) < val(r) && val(r) < val(m) + 8 + val(tlsf_size(hd(m))) → !MEM(r, xs)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_layout"), @lists.mem()]),
        gen,
        strip,
        have(
          "val((h : \{w})) == (a : Num) && 16 <= val(tlsf_size((hd : \{ht})(h)))",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_block_ok((a : Num), (lim : Num), (h : \{w}), (hd : \{ht}))",
              ),
            ),
            rw([thm("tlsf_block_ok")]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        @tactics.first(
          @list.List([
            solve(
              seq([
                subst_only("m"),
                @tactics.disch_tac,
                @tactics.first_x_assum(th => @tactics.disj_cases_tac(th)),
                @tactics.first(
                  @list.List([
                    solve(seq([subst_vars(), @int.asm_arith_tac])),
                    solve(
                      seq([
                        @tactics.mp_tac(
                          inst(thm("tlsf_layout_lower"), [
                            "(t : \{lw})",
                            "(h : \{w})",
                            "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                            "(lim : Num)",
                            "(top : \{w})",
                            "(hd : \{ht})",
                            "(r : \{w})",
                          ]),
                        ),
                        arw([]),
                        @int.asm_arith_tac,
                      ]),
                    ),
                  ]),
                ),
              ]),
            ),
            solve(
              seq([
                @tactics.mp_tac(
                  inst(thm("tlsf_layout_lower"), [
                    "(t : \{lw})",
                    "(h : \{w})",
                    "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                    "(lim : Num)",
                    "(top : \{w})",
                    "(hd : \{ht})",
                    "(m : \{w})",
                  ]),
                ),
                arw([]),
                @tactics.disch_tac,
                have(
                  "!((r : \{w}) == (h : \{w}))",
                  seq([@tactics.disch_tac, subst_vars(), @int.asm_arith_tac]),
                ),
                arw([]),
                @tactics.first_x_assum(th => {
                  @tactics.match_mp_tac(
                    inst(th, [
                      "(h : \{w})",
                      "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                      "(lim : Num)",
                      "(top : \{w})",
                      "(hd : \{ht})",
                      "(m : \{w})",
                      "(r : \{w})",
                    ]),
                  )
                }),
                arw([]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
