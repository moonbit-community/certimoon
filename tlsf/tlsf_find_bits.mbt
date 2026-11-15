// Bitmap masks and trailing-zero selection, including the zero sentinel.

///|
fn prove_tlsf_find_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let xor_ones = lemma(
    "tlsf_xor_ones",
    "∀ x : \{w}, word_xor(x, word(4294967295)) == word_not(x)",
    rw([@equal.gsym(@words.word_reduce_conv(tm("(word_not(word(0)) : \{w})"))), @words.word_xor_not0()]),
  )
  def("tlsf_cut", "tlsf_cut((k : \{w})) == word_xor(word_sub(word_jshl(word(1), k), word(1)), word(4294967295))")
  let cut = lemma(
    "tlsf_cut_not",
    "∀ k : \{w}, tlsf_cut(k) == word_not(word_sub(word_jshl(word(1), k), word(1)))",
    rw([thm("tlsf_cut"), xor_ones]),
  )
  let bits = lemma(
    "tlsf_cut_bits",
    "∀ k : \{w}, ∀ i : Num, val(k) < 32 → (bit(i, tlsf_cut(k)) == (i < 32 && val(k) <= i))",
    seq([
      gen, @tactics.disch_tac,
      have("MOD(val((k : \{w})), 32) == val(k)", seq([@tactics.match_mp_tac(@arith.mod_lt()), arw([])])),
      rw([cut, @words.word_jshl(), @words.word_shl_word(), @arith.mult_clauses(), @words.mask_word_sub(), @words.bit_word_not(), @words.bit_mask_word(), @words.dimindex_32()]),
      arw([]), @int.arith_tac,
    ]),
  )
  let next_bits = lemma(
    "tlsf_cut_next_bits",
    "∀ k : \{w}, ∀ i : Num, val(k) < 32 → (bit(i, word_jshl(tlsf_cut(k), word(1))) ) == (i < 32 && val(k) < i)",
    seq([
      gen, @tactics.disch_tac,
      rw([@words.word_jshl(), @words.val_word_1(), @words.dimindex_32()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      rw([@words.bit_word_shl(), @words.dimindex_32()]),
      @simp.asm_simp_tac(ths([bits])),
      @int.arith_tac,
    ]),
  )
  let cv = lemma(
    "tlsf_ctz_value",
    "∀ x : \{w}, val((word(word_ctz(x)) : \{w})) == word_ctz(x)",
    seq([
      gen,
      @tactics.mp_tac(inst(@words.word_ctz_le_dimindex(), ["(x : \{w})"])),
      rw([@words.dimindex_32(), @words.val_word()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv), @tactics.disch_tac,
      @tactics.match_mp_tac(@arith.mod_lt()), @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_ctz_test",
    "∀ x : \{w}, ((word(word_ctz(x)) : \{w}) == word(32)) == (word_ctz(x) == 32)",
    seq([rw([@equal.gsym(@words.val_eq()), cv, @words.val_word(), @words.dimindex_32()]), @tactics.conv_tac(@calc_num.num_reduce_conv)]),
  )
  let hit = lemma(
    "tlsf_ctz_hit",
    "∀ x : \{w}, word_ctz(x) < 32 → bit(word_ctz(x), x)",
    seq([
      gen, @tactics.disch_tac,
      @tactics.mp_tac(inst(@words.word_ctz_unique_gen(), ["(x : \{w})", "word_ctz((x : \{w}))"])),
      rw([@words.dimindex_32()]), arw([]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let select = lemma(
    "tlsf_ctz_select",
    "∀ x : \{w}, ∀ mask : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, tlsf_sync(x, n, ne) && !(word_ctz(word_and(x, mask)) == 32) → word_ctz(word_and(x, mask)) < n && ne(word_ctz(word_and(x, mask))) && bit(word_ctz(word_and(x, mask)), mask)",
    seq([
      gen, strip,
      have(
        "word_ctz(word_and((x : \{w}), (mask : \{w}))) < 32",
        seq([@tactics.mp_tac(inst(@words.word_ctz_le_dimindex(), ["word_and((x : \{w}), (mask : \{w}))"])), rw([@words.dimindex_32()]), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(inst(hit, ["word_and((x : \{w}), (mask : \{w}))"])),
      arw([@words.bit_word_and()]), strip,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_sync")]))),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_ctz_range",
    "∀ x : \{w}, ∀ mask : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, tlsf_sync(x, n, ne) && !((word(word_ctz(word_and(x, mask))) : \{w}) == word(32)) → val((word(word_ctz(word_and(x, mask))) : \{w})) < n",
    seq([gen, rw([cv, thm("tlsf_ctz_test")]), @meson.meson_tac(ths([select]))]),
  )
  let _ = lemma(
    "tlsf_ctz_plain_range",
    "∀ x : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, tlsf_sync(x, n, ne) && !((word(word_ctz(x)) : \{w}) == word(32)) → val((word(word_ctz(x)) : \{w})) < n",
    seq([
      gen, rw([cv, thm("tlsf_ctz_test")]), strip,
      have("word_ctz((x : \{w})) < 32", seq([@tactics.mp_tac(inst(@words.word_ctz_le_dimindex(), ["(x : \{w})"])), rw([@words.dimindex_32()]), @int.asm_arith_tac])),
      @tactics.mp_tac(inst(hit, ["(x : \{w})"])), arw([]), @tactics.disch_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_sync")]))),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_masked_select",
    "∀ x : \{w}, ∀ k : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, val(k) < 32 && tlsf_sync(x, n, ne) && !(word_ctz(word_and(x, tlsf_cut(k))) == 32) → word_ctz(word_and(x, tlsf_cut(k))) < n && ne(word_ctz(word_and(x, tlsf_cut(k)))) && val(k) <= word_ctz(word_and(x, tlsf_cut(k)))",
    seq([
      gen, strip,
      @tactics.mp_tac(inst(select, ["(x : \{w})", "tlsf_cut((k : \{w}))", "(n : Num)", "(ne : (Num) -> Bool)"])),
      arw([]), strip,
      @tactics.mp_tac(inst(bits, ["(k : \{w})", "word_ctz(word_and((x : \{w}), tlsf_cut((k : \{w}))))"])),
      arw([]), @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_next_select",
    "∀ x : \{w}, ∀ k : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, val(k) < 32 && tlsf_sync(x, n, ne) && !(word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1)))) == 32) → word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1)))) < n && ne(word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1))))) && val(k) < word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1))))",
    seq([
      gen, strip,
      @tactics.mp_tac(inst(select, ["(x : \{w})", "word_jshl(tlsf_cut((k : \{w})), word(1))", "(n : Num)", "(ne : (Num) -> Bool)"])),
      arw([]), strip,
      @tactics.mp_tac(inst(next_bits, ["(k : \{w})", "word_ctz(word_and((x : \{w}), word_jshl(tlsf_cut((k : \{w})), word(1))))"])),
      arw([]), @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_masked_index",
    "∀ x : \{w}, ∀ k : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, val(k) < 32 && tlsf_sync(x, n, ne) && !((word(word_ctz(word_and(x, tlsf_cut(k)))) : \{w}) == word(32)) → val((word(word_ctz(word_and(x, tlsf_cut(k)))) : \{w})) < n && val(k) <= val((word(word_ctz(word_and(x, tlsf_cut(k)))) : \{w}))",
    seq([gen, rw([cv, thm("tlsf_ctz_test")]), @meson.meson_tac(ths([thm("tlsf_masked_select")]))]),
  )
  let _ = lemma(
    "tlsf_next_index",
    "∀ x : \{w}, ∀ k : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, val(k) < 32 && tlsf_sync(x, n, ne) && !((word(word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1))))) : \{w}) == word(32)) → val((word(word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1))))) : \{w})) < n && val(k) < val((word(word_ctz(word_and(x, word_jshl(tlsf_cut(k), word(1))))) : \{w}))",
    seq([gen, rw([cv, thm("tlsf_ctz_test")]), @meson.meson_tac(ths([thm("tlsf_next_select")]))]),
  )
}
