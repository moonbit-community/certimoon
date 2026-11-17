// Extract the pure model facts needed for take, including fit after
// alignment and membership in the selected block's canonical bin.

///|
fn prove_tlsf_take_facts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let facts = "tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht})) && tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt})) && tlsf_tables_sync((fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}"
  let _ = lemma(
    "tlsf_large_facts_frame",
    "\{vars}, ∀ client : \{hprop}, ∀ h : \{heap}, star(\{large}, client, h) → \{facts}",
    () => {
      seq([
        gen,
        rw([thm("tlsf_large"), thm("tlsf_chain"), thm("star")]),
        strip,
        @meson.asm_meson_tac(ths([thm("tlsf_bins_sync")])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_search_aligned_sound",
    "∀ s : \{w}, \{vars}, 16 <= val(s) && val(s) <= 4160749568 && \{facts} → tlsf_find_result(tlsf_align(s), xs, hd, tlsf_search(s, fl, sb, bl))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_align_bounds"), ["(s : \{w})"])),
        arw([]),
        strip,
        have("16 <= val(tlsf_align((s : \{w})))", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("tlsf_search_align"), [
            "(s : \{w})",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        rw([thm("tlsf_find_result")]),
        @tactics.mp_tac(
          inst(thm("tlsf_search_sound"), [
            "tlsf_align((s : \{w}))",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(word(0) : \{w})",
            "tlsf_origin((d : \{w}))",
            "(lim : Num)",
            "(top : \{w})",
            "(xs : \{lw})",
            "(hd : \{ht})",
          ]),
        ),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(ths([thm("tlsf_physical_ok")])),
        ),
        @tactics.repeat_tac(
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "/\\" {
              @tactics.strip_assume_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
        ),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_take_bin_member",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, tlsf_bins_match(xs, hd, bl) && MEM(m, xs) && !tlsf_used(hd(m)) → MEM(m, bl(tlsf_level_of(hd(m)))(tlsf_slot_of(hd(m))))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bins_match")]),
        strip,
        have(
          "tlsf_count((m : \{w}), (bl : \{bt})(tlsf_level_of((hd : \{ht})(m)))(tlsf_slot_of(hd(m)))) == 1",
          @meson.asm_meson_tac(ths([])),
        ),
        rw([thm("tlsf_count_member")]),
        arw([]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
      ])
    },
  )
}
