///|
fn prove_tlsf_split_flags() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let alg = [thm("tlsf_and_or"), thm("tlsf_and_assoc")]
  let zero = [@words.word_and_0(), @words.word_or_0()]
  let norm = seq([rw(alg), @tactics.conv_tac(@words.word_reduce_conv), arw(zero), @tactics.conv_tac(@words.word_reduce_conv), arw([])])
  let low = lemma("tlsf_size_low_bits", "∀ h : \{w}, word_and(tlsf_size(h), word(1)) == word(0) && word_and(tlsf_size(h), word(2)) == word(0) && word_and(tlsf_size(h), word(4294967294)) == tlsf_size(h) && word_and(tlsf_size(h), word(4294967293)) == tlsf_size(h)", seq([
    gen, rw([thm("tlsf_size")]), norm,
  ]))
  let cleanlow = lemma("tlsf_clean_low_bits", "∀ n : \{w}, tlsf_size(n) == n → word_and(n, word(1)) == word(0) && word_and(n, word(2)) == word(0) && word_and(n, word(4294967294)) == n && word_and(n, word(4294967293)) == n", seq([
    gen, @tactics.disch_tac, @tactics.mp_tac(inst(low, ["(n : \{w})"])), arw([]),
  ]))
  let bit2 = @equal.conv_rule(@calc_num.num_reduce_conv, @bool.spec(tm("1"), @words.bit_word_pow2()))
  let flag = lemma("tlsf_last_mask_bit", "∀ h : \{w}, word_and(h, word(2)) == (if bit(1, h) { word(2) } else { word(0) })", seq([
    gen, @class.asm_cases_tac(tm("bit(1, (h : \{w}))")), arw([@words.word_eq_bits(), @words.bit_word_and(), @words.bit_word_0(), bit2, @words.dimindex_32()]),
    gen, @class.asm_cases_tac(tm("(i : Num) == 1")), arw([]), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([]),
  ]))
  let _ = lemma("tlsf_last_mask_cases", "∀ h : \{w}, word_and(h, word(2)) == word(0) || word_and(h, word(2)) == word(2)", seq([
    gen, rw([flag]), @class.asm_cases_tac(tm("bit(1, (h : \{w}))")), arw([]),
  ]))
  let setused = "word_or(word_and((h : \{w}), word(4294967294)), word(1))"
  let _ = lemma("tlsf_used_store_fields", "∀ h : \{w}, tlsf_size(\{setused}) == tlsf_size(h) && (tlsf_last(\{setused}) == tlsf_last(h)) && tlsf_used(\{setused})", seq([
    gen, rw([thm("tlsf_size"), thm("tlsf_last"), thm("tlsf_used")]), norm,
  ]))
  let _ = lemma("tlsf_taken_fields", "∀ n : \{w}, tlsf_size(n) == n → tlsf_size(word_or(n, word(1))) == n && !tlsf_last(word_or(n, word(1))) && tlsf_used(word_or(n, word(1)))", seq([
    gen, @tactics.disch_tac, @tactics.mp_tac(inst(cleanlow, ["(n : \{w})"])), arw([]), strip,
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))), rw([thm("tlsf_size"), thm("tlsf_last"), thm("tlsf_used")]), norm,
  ]))
  let rest = "word_or((s : \{w}), word_and((h : \{w}), word(2)))"
  let _ = lemma("tlsf_remainder_fields", "∀ s : \{w}, ∀ h : \{w}, tlsf_size(s) == s → tlsf_size(\{rest}) == s && (tlsf_last(\{rest}) == tlsf_last(h)) && !tlsf_used(\{rest})", seq([
    gen, @tactics.disch_tac, @tactics.mp_tac(inst(cleanlow, ["(s : \{w})"])), arw([]), strip,
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))), rw([thm("tlsf_size"), thm("tlsf_last"), thm("tlsf_used")]), norm,
  ]))
  let seed = "word_and(word_or((s : \{w}), word_and((old : \{w}), word(3))), word(4294967294))"
  let _ = lemma("tlsf_remainder_seed_size", "∀ s : \{w}, ∀ old : \{w}, tlsf_size(s) == s → tlsf_size(\{seed}) == s", seq([
    gen, @tactics.disch_tac, @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))), rw([thm("tlsf_size")]), norm,
  ]))
  let _ = lemma("tlsf_remainder_seed_clear", "∀ s : \{w}, ∀ old : \{w}, tlsf_size(s) == s → word_and(\{seed}, word(4294967293)) == s", seq([
    gen, @tactics.disch_tac, @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))), norm,
  ]))
  let clean_m = "word_or(word_and(word_or((n : \{w}), word_and(word_and((h : \{w}), word(4294967293)), word(3))), word(4294967294)), word(1))"
  let keep_m = "word_or(word_and(word_or((n : \{w}), word_and((h : \{w}), word(3))), word(4294967294)), word(1))"
  for (name, expr, pre) in [
    ("tlsf_split_taken_last", clean_m, "tlsf_size(n) == n"),
    ("tlsf_split_taken_next", keep_m, "tlsf_size(n) == n && word_and(h, word(2)) == word(0)"),
  ] {
    let _ = lemma(name, "∀ n : \{w}, ∀ h : \{w}, \{pre} → \{expr} == word_or(n, word(1))", seq([
      gen, strip, @tactics.mp_tac(inst(cleanlow, ["(n : \{w})"])), arw([]), strip,
      norm,
    ]))
  }
}
