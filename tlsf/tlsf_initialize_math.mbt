///|
fn prove_tlsf_initialize_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let mask = @equal.conv_rule(
    @words.word_reduce_conv,
    @equal.conv_rule(
      @calc_num.num_reduce_conv,
      inst(@words.val_word_and_not_mask_word(), [
        "word_add((d : \{w}),word(15))",
        "4",
      ]),
    ),
  )
  let _ = lemma(
    "tlsf_initialize_base_value",
    "∀ d : \{w}, val(d) <= 4294965088 → val(tlsf_base(d)) == 16*DIV(val(d)+15,16)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have(
          "val(word_add((d : \{w}),word(15))) == val(d)+15",
          seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        arw([thm("tlsf_base"), mask]),
      ])
    },
  )
  let base = "val(tlsf_base((d : \{w})))"
  let _ = lemma(
    "tlsf_initialize_base_bounds",
    "∀ d : \{w}, val(d) <= 4294965088 → val(d) <= \{base} && \{base} <= 4294965088 && MOD(\{base},16) == 0 && MOD(\{base},8) == 0",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(inst(thm("tlsf_initialize_base_value"), ["(d : \{w})"])),
        arw([]),
        @tactics.disch_tac,
        free_have(
          "DIV(val((d : \{w}))+15,16) <= 268435318",
          seq([
            @tactics.mp_tac(
              inst(@arith.div_mono(), [
                "val((d : \{w}))+15",
                "4294965088+15",
                "16",
              ]),
            ),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @int.asm_arith_tac,
          ]),
        ),
        free_have(
          "val((d : \{w})) <= \{base} && \{base} <= 4294965088",
          seq([
            @tactics.mp_tac(
              inst(@arith.division(), ["val((d : \{w}))+15", "16"]),
            ),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @int.asm_arith_tac,
          ]),
        ),
        free_have("MOD(\{base},16) == 0", arw([@arith.mod_mult()])),
        free_have(
          "MOD(\{base},8) == 0",
          seq([
            @tactics.mp_tac(
              inst(@arith.mod_mod_exp_min(), [base, "2", "4", "3"]),
            ),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        arw([]),
      ])
    },
  )
  let pages = "tlsf_initialize_pages((d : \{w}))"
  let _ = lemma(
    "tlsf_initialize_page_bounds",
    "∀ d : \{w}, val(d) <= 4294965088 → 1 <= \{pages} && \{pages} <= 65536 && \{base}+2208 <= \{pages}*65536 && \{pages}*65536 < \{base}+67744",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_initialize_base_bounds"), ["(d : \{w})"]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(inst(@arith.division(), [base, "65536"])),
        @tactics.mp_tac(
          inst(@arith.division(), ["MOD(\{base},65536)+67743", "65536"]),
        ),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        strip,
        rw([thm("tlsf_initialize_pages")]),
        @int.asm_arith_tac,
      ])
    },
  )
  let m = "tlsf_initialize_origin((d : \{w}))"
  let _ = lemma(
    "tlsf_initialize_origin_value",
    "∀ d : \{w}, val(d) <= 4294965088 → val(\{m}) == tlsf_origin(d) && !(\{m} == word(0)) && MOD(val(\{m}),8) == 0",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_initialize_base_bounds"), ["(d : \{w})"]),
        ),
        arw([]),
        strip,
        free_have(
          "val(\{m}) == \{base}+2176",
          seq([
            rw([thm("tlsf_initialize_origin")]),
            @tactics.match_mp_tac(thm("val_add_small")),
            @int.asm_arith_tac,
          ]),
        ),
        @tactics.mp_tac(inst(@arith.mod_add_mod(), [base, "2176", "8"])),
        arw([
          thm("tlsf_origin"),
          @equal.gsym(@words.val_eq()),
          @words.val_word_0(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let shr16 = @logic.prove(
    tm("∀ x : \{w}, val(word_jushr(x,word(16))) == DIV(val(x),65536)"),
    seq([
      gen,
      rw([
        @words.word_jushr(),
        @words.val_word_ushr(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  let low = "word_and(tlsf_base((d : \{w})),word(65535))"
  let mask16 = @equal.conv_rule(
    @words.word_reduce_conv,
    @equal.conv_rule(
      @calc_num.num_reduce_conv,
      inst(@words.val_word_and_mask_word(), ["tlsf_base((d : \{w}))", "16"]),
    ),
  )
  let _ = lemma(
    "tlsf_initialize_required_value",
    "∀ d : \{w}, val(d) <= 4294965088 → val(tlsf_initialize_required(d)) == tlsf_initialize_pages(d)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        have("val(\{low}) == MOD(\{base},65536)", @tactics.accept_tac(mask16)),
        have(
          "MOD(\{base},65536) < 65536",
          seq([
            @tactics.mp_tac(inst(@arith.division(), [base, "65536"])),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @meson.meson_tac(ths([])),
          ]),
        ),
        have(
          "val(word_add(\{low},word(67743))) == MOD(\{base},65536)+67743",
          seq([
            @tactics.mp_tac(inst(thm("val_add_small"), [low, "67743"])),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_initialize_page_bounds"), ["(d : \{w})"]),
        ),
        arw([thm("tlsf_initialize_pages")]),
        strip,
        rw([thm("tlsf_initialize_required")]),
        @simp.once_rewrite_tac(ths([@words.val_word_add()])),
        arw([@words.dimindex_32(), shr16]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([thm("tlsf_initialize_pages")]),
        @tactics.match_mp_tac(@arith.mod_lt()),
        @int.asm_arith_tac,
      ])
    },
  )
}
