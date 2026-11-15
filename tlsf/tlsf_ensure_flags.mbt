///|
fn prove_tlsf_ensure_flags() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let alg = [thm("tlsf_and_or"), thm("tlsf_and_assoc")]
  let norm = seq([
    rw(alg),
    @tactics.conv_tac(@words.word_reduce_conv),
    arw([@words.word_and_0(), @words.word_or_0()]),
    @tactics.conv_tac(@words.word_reduce_conv),
    arw([]),
  ])
  let sized = "word_or((z : \{w}),word_and((h : \{w}),word(3)))"
  let _ = lemma(
    "tlsf_resized_fields",
    "∀ z : \{w}, ∀ h : \{w}, tlsf_size(z) == z → tlsf_size(\{sized}) == z && (tlsf_used(\{sized}) == tlsf_used(h)) && (tlsf_last(\{sized}) == tlsf_last(h))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_clean_low_bits"), ["(z : \{w})"])),
      arw([]),
      strip,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))),
      rw([thm("tlsf_size"), thm("tlsf_used"), thm("tlsf_last")]),
      norm,
    ]),
  )
  let clear = "word_and((h : \{w}),word(4294967293))"
  let _ = lemma(
    "tlsf_clear_last_fields",
    "∀ h : \{w}, tlsf_size(\{clear}) == tlsf_size(h) && (tlsf_used(\{clear}) == tlsf_used(h)) && !tlsf_last(\{clear})",
    seq([gen, rw([thm("tlsf_size"), thm("tlsf_used"), thm("tlsf_last")]), norm]),
  )
  let last = "word_or((z : \{w}),word(2))"
  let _ = lemma(
    "tlsf_new_top_fields",
    "∀ z : \{w}, tlsf_size(z) == z → tlsf_size(\{last}) == z && !tlsf_used(\{last}) && tlsf_last(\{last})",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_clean_low_bits"), ["(z : \{w})"])),
      arw([]),
      strip,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))),
      rw([thm("tlsf_size"), thm("tlsf_used"), thm("tlsf_last")]),
      norm,
    ]),
  )
}
