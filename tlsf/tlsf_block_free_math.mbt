// All scalar operations stay in the small range 0..256; addresses are
// checked separately against memory32 and the linked table base.

///|
fn prove_tlsf_block_free_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_class_bounds",
    "∀ s : Num, 8 <= s && s <= 256 && MOD(s,8) == 0 → 1 <= DIV(s,8) && DIV(s,8) < 33 && s == 8*DIV(s,8) && DIV(s+7,8) == DIV(s,8)",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(@arith.division(), ["(s : Num)", "8"])),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([]),
        strip,
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(@int.asm_arith_tac),
            solve(
              seq([
                @tactics.match_mp_tac(
                  inst(@arith.div_uniq(), [
                    "(s : Num)+7", "8", "DIV((s : Num),8)", "7",
                  ]),
                ),
                @int.asm_arith_tac,
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let c = "word_jushr(word_add((s : \{w}),word(7)),word(3))"
  let _ = lemma(
    "tlsf_small_class_word",
    "∀ s : \{w}, 8 <= val(s) && val(s) <= 256 && MOD(val(s),8) == 0 → \{c} == word(DIV(val(s),8))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_small_class_bounds"), ["val((s : " + w + "))"]),
        ),
        arw([]),
        strip,
        free_have(
          "val(word_add((s : \{w}),word(7))) == val(s)+7",
          seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        free_have("DIV(val((s : \{w})),8) < 4294967296", @int.asm_arith_tac),
        rw([
          @equal.gsym(@words.val_eq()),
          @words.word_jushr(),
          @words.val_word_ushr(),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([]),
        @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_word_eq",
    "∀ m : Num, ∀ n : Num, m <= 66 && n <= 66 → (((word(m) : \{w}) == word(n)) == (m == n))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "(m : Num) < 4294967296 && (n : Num) < 4294967296", @int.asm_arith_tac,
        ),
        rw([
          @equal.gsym(@words.val_eq()),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_word_dec",
    "∀ n : Num, 1 <= n → word_sub((word(n) : \{w}),word(1)) == word(n-1)",
    () => seq([gen, @tactics.disch_tac, arw([@words.word_sub_v1()])]),
  )
}
