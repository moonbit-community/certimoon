///|
fn prove_tlsf_take_math() -> Unit raise {
  let w = w32
  let bt = "(Num) -> (Num) -> List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_align_mod",
    "∀ s : \{w}, val(s) <= 4160749568 → MOD(val(tlsf_align(s)), 16) == 0",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_align_value"), ["(s : \{w})"])),
      arw([]),
      @tactics.disch_then(th => @tactics.subst1_tac(th)),
      rw([@arith.mod_mult()]),
    ]),
  )
  let _ = lemma(
    "tlsf_align_fixed",
    "∀ s : \{w}, val(s) <= 4160749568 && MOD(val(s), 16) == 0 → tlsf_align(s) == s",
    seq([
      gen,
      strip,
      rw([@equal.gsym(@words.val_eq())]),
      @tactics.mp_tac(inst(thm("tlsf_align_value"), ["(s : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      have(
        "DIV(val((s : \{w})) + 15, 16) == DIV(val(s), 16)",
        seq([
          @tactics.match_mp_tac(
            @simp.rewrite_rule(ths([@arith.add_clauses()]))(
              @equal.conv_rule(
                @calc_num.num_reduce_conv,
                inst(@arith.div_add_eq(), ["16", "val((s : \{w}))", "15"]),
              ),
            ),
          ),
          arw([]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
        ]),
      ),
      @tactics.mp_tac(inst(@arith.division(), ["val((s : \{w}))", "16"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_align_idem",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= 4160749568 → tlsf_align(tlsf_align(s)) == tlsf_align(s)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_align_bounds"), ["(s : \{w})"])),
      arw([]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_align_fixed")),
      arw([]),
      @tactics.match_mp_tac(thm("tlsf_align_mod")),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_search_align",
    "∀ s : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, 16 <= val(s) && val(s) <= 4160749568 → tlsf_search(tlsf_align(s), fl, sb, bl) == tlsf_search(s, fl, sb, bl)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_align_idem"), ["(s : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      rw([thm("tlsf_search"), thm("tlsf_search_f"), thm("tlsf_search_j")]),
      arw([]),
    ]),
  )
}
