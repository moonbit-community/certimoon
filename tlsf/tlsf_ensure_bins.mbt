// Publish one new free block, or republish a detached block after resizing.

///|
fn prove_tlsf_ensure_bins() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let other = thm("tlsf_bin_add_count_other")
  let point = (proofs : Array[@kernel.Thm]) => {
    seq([
      seq(proofs.map(@tactics.assume_tac)),
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
  }
  let cov = @kernel.assume_rule(
    tm(
      "∀ x : \{w}, MEM(x, (xs : \{lw})) && !tlsf_used((hd : \{ht})(x)) → tlsf_count(x, (bl : \{bt})(tlsf_level_of(hd(x)))(tlsf_slot_of(hd(x)))) == 1",
    ),
  )
  let snd = @kernel.assume_rule(
    tm(
      "∀ i : Num, ∀ k : Num, ∀ x : \{w}, i < 28 && k < 16 && MEM(x, (bl : \{bt})(i)(k)) → MEM(x, (xs : \{lw})) && !tlsf_used((hd : \{ht})(x)) && tlsf_level_of(hd(x)) == i && tlsf_slot_of(hd(x)) == k",
    ),
  )
  let rel = @kernel.assume_rule(
    tm(
      "∀ x : \{w}, !(x == (r : \{w})) → ((MEM(x, (xs : \{lw})) && !tlsf_used((hd : \{ht})(x))) == (MEM(x, (ys : \{lw})) && !tlsf_used((nh : \{ht})(x)))) && (MEM(x, xs) && !tlsf_used(hd(x)) → tlsf_level_of(hd(x)) == tlsf_level_of(nh(x)) && tlsf_slot_of(hd(x)) == tlsf_slot_of(nh(x)))",
    ),
  )
  let _ = lemma(
    "tlsf_bins_match_publish",
    "∀ xs : \{lw}, ∀ ys : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, ∀ bl : \{bt}, ∀ r : \{w}, ∀ f : Num, ∀ j : Num, tlsf_bins_match(xs, hd, bl) && !(MEM(r, xs) && !tlsf_used(hd(r))) && f < 28 && j < 16 && MEM(r, ys) && !tlsf_used(nh(r)) && tlsf_level_of(nh(r)) == f && tlsf_slot_of(nh(r)) == j && (∀ m : \{w}, !(m == r) → ((MEM(m, xs) && !tlsf_used(hd(m))) == (MEM(m, ys) && !tlsf_used(nh(m)))) && (MEM(m, xs) && !tlsf_used(hd(m)) → tlsf_level_of(hd(m)) == tlsf_level_of(nh(m)) && tlsf_slot_of(hd(m)) == tlsf_slot_of(nh(m)))) → tlsf_bins_match(ys, nh, tlsf_bin_add(bl, f, j, r))",
    () => {
      seq([
        gen,
        strip,
        @tactics.undisch_tac(
          tm("tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt}))"),
        ),
        rw([thm("tlsf_bins_match")]),
        strip,
        rw([thm("tlsf_bins_match")]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              gen,
              strip,
              @class.asm_cases_tac(tm("(m : \{w}) == (r : \{w})")),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      have(
                        "tlsf_count((r : \{w}), (bl : \{bt})((f : Num))((j : Num))) == 0",
                        seq([
                          rw([thm("tlsf_count_zero")]),
                          point([
                            inst(snd, ["(f : Num)", "(j : Num)", "(r : \{w})"]),
                          ]),
                        ]),
                      ),
                      arw([thm("tlsf_bin_add"), thm("tlsf_count_cons")]),
                      @tactics.conv_tac(@calc_num.num_reduce_conv),
                    ]),
                  ),
                  solve(
                    seq([
                      @simp.asm_simp_tac(ths([other])),
                      point([
                        inst(cov, ["(m : \{w})"]),
                        inst(rel, ["(m : \{w})"]),
                      ]),
                    ]),
                  ),
                ]),
              ),
            ]),
            seq([
              gen,
              rw([thm("tlsf_bin_add_mem")]),
              strip,
              point([
                inst(snd, ["(f' : Num)", "(j' : Num)", "(m : \{w})"]),
                inst(rel, ["(m : \{w})"]),
              ]),
            ]),
          ]),
        ),
      ])
    },
  )
}
