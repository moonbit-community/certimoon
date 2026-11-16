// Relate the compiler's shifted size-class table address to the abstract
// 33-entry small table, with no wrapping addresses.

///|
fn prove_tlsf_block_free_addresses() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_class_shift",
    "∀ k : Num, k < 33 → word_jshl((word(k) : \{w}),word(3)) == word(8*k)",
    seq([
      gen,
      @tactics.disch_tac,
      free_have("(k : Num) < 4294967296", @int.asm_arith_tac),
      rw([
        @words.word_jshl(),
        @words.word_shl(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt(), @arith.mult_sym()])),
    ]),
  )
  let cls = "word_jushr(word_add((word(s) : \{w}),word(7)),word(3))"
  let table = "word_add(word_add(tlsf_base((d : \{w})),word_jshl(\{cls},word(3))),word(1916))"
  let _ = lemma(
    "tlsf_small_table_address",
    "∀ d : \{w}, ∀ s : Num, val(d) <= 4294965088 && 8 <= s && s <= 256 && MOD(s,8) == 0 → \{cls} == word(DIV(s,8)) && val(\{table}) == val(tlsf_base(d))+1916+8*DIV(s,8)",
    seq([
      gen,
      strip,
      g => {
        @tactics.strip_assume_tac(
          block_under(inst(thm("tlsf_small_class_bounds"), ["(s : Num)"]), g),
        )(g)
      },
      free_have(
        "val((word((s : Num)) : \{w})) == s",
        seq([
          rw([@words.val_word(), @words.dimindex_32()]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @tactics.match_mp_tac(@arith.mod_lt()),
          @int.asm_arith_tac,
        ]),
      ),
      free_have(
        "\{cls} == (word(DIV((s : Num),8)) : \{w})",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_small_class_word"), ["(word((s : Num)) : " + w + ")"]),
          ),
          arw([]),
        ]),
      ),
      arw([]),
      free_have(
        "word_jshl((word(DIV((s : Num),8)) : \{w}),word(3)) == word(8*DIV(s,8))",
        seq([@tactics.match_mp_tac(thm("tlsf_small_class_shift")), arw([])]),
      ),
      arw([]),
      free_have(
        "word_add(word_add(tlsf_base((d : \{w})),word(8*DIV((s : Num),8))),word(1916)) == word_add(tlsf_base(d),word(1916+8*DIV(s,8)))",
        seq([
          rw([@words.word_add_v1(), @words.word_mul_v1()]),
          g => @tactics.accept_tac(@words.word_rule(g.1))(g),
        ]),
      ),
      arw([]),
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_offset"), [
          "(d : " + w + ")",
          "1916+8*DIV((s : Num),8)",
        ]),
      ),
      free_have("1916+8*DIV((s : Num),8) <= 2176", @int.asm_arith_tac),
      arw([]),
      @int.arith_tac,
    ]),
  )
}
