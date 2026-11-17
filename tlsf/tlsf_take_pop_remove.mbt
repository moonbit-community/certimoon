///|
fn prove_tlsf_take_pop_remove() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_pop_bl_at",
    "∀ h : \{w}, ∀ bl : \{bt}, ∀ xs : \{lw}, ∀ i : Num, ∀ j : Num, tlsf_pop_bl(h, bl, xs, i, j) == (if i == tlsf_level_of(h) && j == tlsf_slot_of(h) { xs } else { bl(i)(j) })",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_pop_bl"),
          thm("tlsf_upd"),
          thm("tlsf_level_of"),
          thm("tlsf_slot_of"),
        ]),
        @class.cond_cases_tac,
        arw([]),
        @class.cond_cases_tac,
        arw([]),
      ])
    },
  )
  let xs = "(xs : \{lw})"
  let hd = "(hd : \{ht})"
  let bl = "(bl : \{bt})"
  let m = "(m : \{w})"
  let scalar = "\{hd}(\{m})"
  let f = "tlsf_level_of(\{scalar})"
  let j = "tlsf_slot_of(\{scalar})"
  let before = "APPEND((us : \{lw}), CONS(\{m}, (vs : \{lw})))"
  let after = "APPEND((us : \{lw}), (vs : \{lw}))"
  let nb = "tlsf_pop_bl(\{scalar}, \{bl}, \{after})"
  let oldmatch = "tlsf_bins_match(\{xs}, \{hd}, \{bl})"
  let cov = @simp.rewrite_rule(ths([thm("tlsf_bins_match")]))(
    @kernel.assume_rule(tm(oldmatch)),
  )
  let cov = @bool.spec(tm(m), @bool.conjunct1(cov))
  let _ = lemma(
    "tlsf_pop_bins_match",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, ∀ us : \{lw}, ∀ vs : \{lw}, \{oldmatch} && MEM(m, xs) && !tlsf_used(hd(m)) && bl(\{f})(\{j}) == \{before} → tlsf_bins_match(xs, tlsf_mark(hd, m), \{nb})",
    () => {
      seq([
        gen,
        strip,
        have(
          "tlsf_count(\{m}, \{before}) == 1",
          seq([@tactics.mp_tac(cov), arw([])]),
        ),
        @tactics.match_mp_tac(
          inst(thm("tlsf_bins_match_detach"), [xs, hd, bl, nb, m]),
        ),
        arw([]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              gen,
              @tactics.disch_tac,
              @tactics.match_mp_tac(
                inst(thm("tlsf_pop_bl_other_count"), [
                  scalar,
                  bl,
                  "(us : \{lw})",
                  "(vs : \{lw})",
                  m,
                  "(x : \{w})",
                  "(i : Num)",
                  "(j : Num)",
                ]),
              ),
              arw([]),
            ]),
            seq([
              gen,
              strip,
              rw([thm("tlsf_pop_bl_at")]),
              @class.cond_cases_tac,
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      @tactics.match_mp_tac(
                        inst(thm("tlsf_remove_self_count"), [
                          "(us : \{lw})",
                          "(vs : \{lw})",
                          m,
                        ]),
                      ),
                      arw([]),
                    ]),
                  ),
                  solve(
                    seq([
                      have(
                        "!(\{f} == (i : Num) && \{j} == (j : Num))",
                        @meson.asm_meson_tac(ths([])),
                      ),
                      @tactics.mp_tac(
                        inst(thm("tlsf_bins_match_exact"), [
                          xs, hd, bl, m, "(i : Num)", "(j : Num)",
                        ]),
                      ),
                      arw([]),
                    ]),
                  ),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
