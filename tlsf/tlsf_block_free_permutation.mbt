// Exact occurrence counts determine the commutative heap fold. This is used
// when the last release recovers a page whose local list has arbitrary order.

///|
fn prove_tlsf_block_free_permutation() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ft = "(\{w}) -> \{hprop}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_count_empty",
    "∀ xs : \{lw}, (∀ q : \{w}, tlsf_count(q,xs) == 0) → xs == NIL",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([@lists.not_cons_nil()]),
        strip,
        @tactics.first_x_assum(th => {
          @tactics.mp_tac(@bool.spec(tm("(h : " + w + ")"), th))
        }),
        rw([thm("tlsf_small_count_cons")]),
        @int.arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_hlist_permutation",
    "∀ xs : \{lw}, ∀ ff : \{ft}, ∀ ys : \{lw}, (∀ q : \{w}, tlsf_count(q,xs) == tlsf_count(q,ys)) && (∀ q : \{w}, MEM(q,xs) → tlsf_count(q,xs) == 1) → tlsf_small_hlist(ff,xs) == tlsf_small_hlist(ff,ys)",
    () => {
      @tactics.thenl(
        @lists.list_induct_tac,
        @list.List([
          seq([
            gen,
            rw([thm("tlsf_count"), @lists.filter(), @lists.length()]),
            strip,
            free_have(
              "(ys : \{lw}) == NIL",
              seq([
                @tactics.match_mp_tac(thm("tlsf_small_count_empty")),
                gen,
                rw([thm("tlsf_count")]),
                small_meson(ths([])),
              ]),
            ),
            arw([]),
          ]),
          seq([
            gen,
            strip,
            free_have(
              "tlsf_count((h : \{w}),CONS(h,(t : \{lw}))) == 1",
              small_meson(ths([@lists.mem()])),
            ),
            free_have(
              "tlsf_count((h : \{w}),(t : \{lw})) == 0",
              seq([
                @tactics.undisch_tac(
                  tm(
                    "tlsf_count((h : " + w + "),CONS(h,(t : " + lw + "))) == 1",
                  ),
                ),
                rw([thm("tlsf_small_count_cons")]),
                @int.arith_tac,
              ]),
            ),
            free_have(
              "tlsf_count((h : \{w}),(ys : \{lw})) == 1",
              small_meson(ths([])),
            ),
            free_have(
              "∀ q : \{w}, tlsf_count(q,(t : \{lw})) == tlsf_count(q,tlsf_small_remove((h : \{w}),(ys : \{lw})))",
              seq([
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                rw([thm("tlsf_small_remove_count")]),
                @class.cond_cases_tac,
                subst_vars(),
                arw([]),
                @tactics.mp_tac(
                  @bool.spec(
                    tm("(q : " + w + ")"),
                    @kernel.assume_rule(
                      tm(
                        "∀ q : " +
                        w +
                        ", tlsf_count(q,CONS((h : " +
                        w +
                        "),(t : " +
                        lw +
                        "))) == tlsf_count(q,(ys : " +
                        lw +
                        "))",
                      ),
                    ),
                  ),
                ),
                rw([thm("tlsf_small_count_cons")]),
                arw([]),
                small_meson(ths([@theorems.eq_sym_eq(), @arith.add_clauses()])),
              ]),
            ),
            free_have(
              "∀ q : \{w}, MEM(q,(t : \{lw})) → tlsf_count(q,t) == 1",
              seq([
                gen,
                @tactics.disch_tac,
                free_have(
                  "tlsf_count((q : \{w}),CONS((h : \{w}),(t : \{lw}))) == 1",
                  small_meson(ths([@lists.mem()])),
                ),
                free_have(
                  "!((h : \{w}) == (q : \{w}))",
                  small_meson(ths([thm("tlsf_count_zero")])),
                ),
                @tactics.accept_tac(
                  @simp.rewrite_rule(
                    ths([
                      thm("tlsf_small_count_cons"),
                      @kernel.assume_rule(
                        tm("!((h : " + w + ") == (q : " + w + "))"),
                      ),
                      @arith.add_clauses(),
                    ]),
                  )(
                    @kernel.assume_rule(
                      tm(
                        "tlsf_count((q : " +
                        w +
                        "),CONS((h : " +
                        w +
                        "),(t : " +
                        lw +
                        "))) == 1",
                      ),
                    ),
                  ),
                ),
              ]),
            ),
            @tactics.mp_tac(
              inst(thm("tlsf_small_hlist_focus"), [
                "(ys : " + lw + ")",
                "(ff : " + ft + ")",
                "(h : " + w + ")",
              ]),
            ),
            arw([]),
            @tactics.disch_tac,
            arw([thm("tlsf_small_hlist")]),
            @tactics.ap_term_tac,
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            arw([]),
          ]),
        ]),
      )
    },
  )
}
