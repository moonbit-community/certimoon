///|
fn prove_tlsf_split_arithmetic() -> Unit raise {
  let w = w32
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  for (name, big, small, be, se) in [("tlsf_mod16_8", 16, 8, 4, 3), ("tlsf_mod8_4", 8, 4, 3, 2)] {
    let _ = lemma(name, "∀ x : Num, MOD(x, \{big}) == 0 → MOD(x, \{small}) == 0", seq([
      gen, @tactics.disch_tac, @tactics.mp_tac(inst(@arith.mod_mod_exp_min(), ["(x : Num)", "2", be.to_string(), se.to_string()])), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([]), @int.asm_arith_tac,
    ]))
  }
  let add = lemma("tlsf_val_add_exact", "∀ x : \{w}, ∀ y : \{w}, val(x) + val(y) < 4294967296 → val(word_add(x, y)) == val(x) + val(y)", seq([
    gen, @tactics.disch_tac, rw([@words.val_word_add(), @words.dimindex_32()]), @tactics.conv_tac(@calc_num.num_reduce_conv), @simp.asm_simp_tac(ths([@arith.mod_lt()])),
  ]))
  let _ = lemma("tlsf_split_test", "∀ h : \{w}, ∀ n : \{w}, val(n) <= 4160749568 → (word_ugt(tlsf_size(h), word_add(n, word(264))) == (val(n) + 264 < val(tlsf_size(h))))", seq([
    gen, @tactics.disch_tac,
    have("val(word_add((n : \{w}), word(264))) == val(n) + 264", seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac])),
    rw([@words.word_ugt_v1()]), arw([]), @int.arith_tac,
  ]))
  let align_sub = lemma("tlsf_aligned_sub", "∀ z : Num, ∀ n : Num, MOD(z, 8) == 0 && MOD(n, 8) == 0 && n + 8 <= z → MOD(z - n - 8, 8) == 0", seq([
    gen, strip,
    @tactics.mp_tac(inst(@arith.division(), ["(z : Num)", "8"])),
    @tactics.mp_tac(inst(@arith.division(), ["(n : Num)", "8"])), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([]), strip,
    have("DIV((n : Num), 8) + 1 <= DIV((z : Num), 8)", @int.asm_arith_tac),
    have("(z : Num) - (n : Num) - 8 == 8 * (DIV(z, 8) - DIV(n, 8) - 1)", seq([rw([@arith.left_sub_distrib()]), @int.asm_arith_tac])),
    @tactics.first_x_assum(th => if @basics.aconv(@equal.lhs(@kernel.concl(th)), tm("(z : Num) - (n : Num) - 8")) { @tactics.subst1_tac(th) } else { @tactics.no_tac }), rw([@arith.mod_mult()]),
  ]))
  let _ = lemma("tlsf_remainder_value", "∀ h : \{w}, ∀ n : \{w}, val(n) + 8 <= val(tlsf_size(h)) → val(tlsf_remainder_size(h, n)) == val(tlsf_size(h)) - val(n) - 8", seq([
    gen, @tactics.disch_tac,
    have("val((n : \{w})) <= val(tlsf_size((h : \{w})))", @int.asm_arith_tac),
    have("val(word_sub(tlsf_size((h : \{w})), (n : \{w}))) == val(tlsf_size(h)) - val(n)", seq([rw([@words.val_word_sub_cases()]), arw([])])),
    have("8 <= val(tlsf_size((h : \{w}))) - val((n : \{w}))", @int.asm_arith_tac),
    rw([thm("tlsf_remainder_size"), @words.val_word_sub_cases(), @words.val_word(), @words.dimindex_32()]), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([]),
  ]))
  let r = "tlsf_remainder((m : \{w}), (n : \{w}))"
  let rem = "tlsf_remainder_size((hd : \{ht})((m : \{w})), (n : \{w}))"
  let sz = "val(tlsf_size((hd : \{ht})((m : \{w}))))"
  let _ = lemma("tlsf_split_bounds", "∀ m : \{w}, ∀ n : \{w}, ∀ hd : \{ht}, ∀ lim : Num, tlsf_block_ok(val(m), lim, m, hd) && lim <= 4294967296 && 16 <= val(n) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) + 264 < \{sz} → val(\{r}) == val(m) + 8 + val(n) && !(\{r} == word(0)) && !(\{r} == m) && MOD(val(\{r}), 8) == 0 && val(\{rem}) == \{sz} - val(n) - 8 && 16 <= val(\{rem}) && MOD(val(\{rem}), 8) == 0 && tlsf_size(n) == n && tlsf_size(\{rem}) == \{rem} && val(n) + 8 + val(\{rem}) == \{sz}", seq([
    gen, rw([thm("tlsf_block_ok")]), strip,
    have("MOD(val((n : \{w})), 8) == 0", seq([@tactics.match_mp_tac(thm("tlsf_mod16_8")), arw([])])),
    have("MOD(val((n : \{w})), 4) == 0", seq([@tactics.match_mp_tac(thm("tlsf_mod8_4")), arw([])])),
    have("tlsf_size((n : \{w})) == n", seq([rw([thm("tlsf_size_clean")]), arw([])])),
    have("val((n : \{w})) + 8 <= \{sz}", @int.asm_arith_tac),
    @tactics.mp_tac(inst(thm("tlsf_remainder_value"), ["(hd : \{ht})((m : \{w}))", "(n : \{w})"])), arw([]), @tactics.disch_tac,
    have("tlsf_size(\{rem}) == \{rem}", seq([@tactics.match_mp_tac(inst(thm("tlsf_remainder_mask"), ["(hd : \{ht})((m : \{w}))", "(n : \{w})"])), arw([])])),
    have("MOD(val(\{rem}), 8) == 0", seq([arw([]), @tactics.match_mp_tac(align_sub), arw([])])),
    have("val(word_add((m : \{w}), word(8))) == val(m) + 8", seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac])),
    have("val((n : \{w})) + val(word_add((m : \{w}), word(8))) < 4294967296", @int.asm_arith_tac),
    @tactics.mp_tac(inst(add, ["(n : \{w})", "word_add((m : \{w}), word(8))"])), arw([]),
    @tactics.disch_tac,
    have("val(\{r}) == val((m : \{w})) + 8 + val((n : \{w}))", seq([rw([thm("tlsf_remainder")]), @int.asm_arith_tac])),
    have("!(\{r} == word(0))", seq([rw([@equal.gsym(@words.val_eq_0())]), @int.asm_arith_tac])),
    have("!(\{r} == (m : \{w}))", seq([rw([@equal.gsym(@words.val_eq())]), @int.asm_arith_tac])),
    have("MOD(val(\{r}), 8) == 0", seq([
      @tactics.mp_tac(inst(@arith.mod_add_mod(), ["val((m : \{w})) + 8", "val((n : \{w}))", "8"])),
      @tactics.mp_tac(inst(@arith.mod_add_mod(), ["val((m : \{w}))", "8", "8"])), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([]), @int.asm_arith_tac,
    ])), arw([]), @int.asm_arith_tac,
  ]))
}
