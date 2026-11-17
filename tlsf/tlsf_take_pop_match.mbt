///|
fn prove_tlsf_take_pop_match() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let marked = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let oldcov = @kernel.assume_rule(
    tm(
      "∀ x : \{w}, MEM(x, (xs : \{lw})) && !tlsf_used((hd : \{ht})(x)) → tlsf_count(x, (bl : \{bt})(tlsf_level_of(hd(x)))(tlsf_slot_of(hd(x)))) == 1",
    ),
  )
  let oldsnd = @kernel.assume_rule(
    tm(
      "∀ i : Num, ∀ j : Num, ∀ x : \{w}, i < 28 && j < 16 && MEM(x, (bl : \{bt})(i)(j)) → MEM(x, (xs : \{lw})) && !tlsf_used((hd : \{ht})(x)) && tlsf_level_of(hd(x)) == i && tlsf_slot_of(hd(x)) == j",
    ),
  )
  let countother = @kernel.assume_rule(
    tm(
      "∀ x : \{w}, ∀ i : Num, ∀ j : Num, !(x == (m : \{w})) → tlsf_count(x, (nb : \{bt})(i)(j)) == tlsf_count(x, (bl : \{bt})(i)(j))",
    ),
  )
  let countzero = @kernel.assume_rule(
    tm(
      "∀ i : Num, ∀ j : Num, i < 28 && j < 16 → tlsf_count((m : \{w}), (nb : \{bt})(i)(j)) == 0",
    ),
  )
  let ground = seq([
    @tactics.pop_assum_list(all => {
      seq(
        all
        .to_array()
        .filter(th => !@basics.is_forall(@kernel.concl(th)))
        .map(@tactics.assume_tac),
      )
    }),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "tlsf_bins_match_detach",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ nb : \{bt}, ∀ m : \{w}, tlsf_bins_match(xs, hd, bl) && (∀ x : \{w}, ∀ i : Num, ∀ j : Num, !(x == m) → tlsf_count(x, nb(i)(j)) == tlsf_count(x, bl(i)(j))) && (∀ i : Num, ∀ j : Num, i < 28 && j < 16 → tlsf_count(m, nb(i)(j)) == 0) → tlsf_bins_match(xs, \{marked}, nb)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bins_match")]),
        strip,
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              gen,
              strip,
              @class.asm_cases_tac(tm("(m' : \{w}) == (m : \{w})")),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      subst_vars(),
                      @tactics.assume_tac(
                        inst(thm("tlsf_mark_used"), [
                          "(hd : \{ht})",
                          "(m : \{w})",
                        ]),
                      ),
                      ground,
                    ]),
                  ),
                  solve(
                    seq([
                      @tactics.rule_assum_tac(
                        @simp.rewrite_rule(
                          ths([
                            @bool.undisch(
                              inst(thm("tlsf_mark_other"), [
                                "(hd : \{ht})",
                                "(m : \{w})",
                                "(m' : \{w})",
                              ]),
                            ),
                          ]),
                        ),
                      ),
                      @tactics.assume_tac(inst(oldcov, ["(m' : \{w})"])),
                      @tactics.assume_tac(
                        inst(countother, [
                          "(m' : \{w})",
                          "tlsf_level_of((hd : \{ht})((m' : \{w})))",
                          "tlsf_slot_of((hd : \{ht})((m' : \{w})))",
                        ]),
                      ),
                      rw([thm("tlsf_mark"), thm("tlsf_put")]),
                      arw([]),
                      ground,
                    ]),
                  ),
                ]),
              ),
            ]),
            seq([
              gen,
              strip,
              have(
                "!((m' : \{w}) == (m : \{w}))",
                seq([
                  @tactics.assume_tac(
                    inst(countzero, ["(f : Num)", "(j : Num)"]),
                  ),
                  @tactics.assume_tac(
                    inst(thm("tlsf_count_zero"), [
                      "(m : \{w})",
                      "(nb : \{bt})((f : Num))((j : Num))",
                    ]),
                  ),
                  ground,
                ]),
              ),
              have(
                "MEM((m' : \{w}), (bl : \{bt})((f : Num))((j : Num)))",
                seq([
                  @tactics.assume_tac(
                    inst(countother, ["(m' : \{w})", "(f : Num)", "(j : Num)"]),
                  ),
                  @tactics.assume_tac(
                    inst(thm("tlsf_count_member"), [
                      "(m' : \{w})",
                      "(nb : \{bt})((f : Num))((j : Num))",
                    ]),
                  ),
                  @tactics.assume_tac(
                    inst(thm("tlsf_count_member"), [
                      "(m' : \{w})",
                      "(bl : \{bt})((f : Num))((j : Num))",
                    ]),
                  ),
                  ground,
                ]),
              ),
              rw([thm("tlsf_mark"), thm("tlsf_put")]),
              arw([]),
              @tactics.assume_tac(
                inst(oldsnd, ["(f : Num)", "(j : Num)", "(m' : \{w})"]),
              ),
              ground,
            ]),
          ]),
        ),
      ])
    },
  )
}
