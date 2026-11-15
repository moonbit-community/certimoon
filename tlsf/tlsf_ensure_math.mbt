///|
fn prove_tlsf_ensure_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let s = "(s : \{w})"
  let r = "tlsf_round(\{s})"
  let k = "EXP(2,val(tlsf_fli(\{r}))-4)"
  let j = "val(tlsf_sli(\{r},tlsf_fli(\{r})))"
  let _ = lemma(
    "tlsf_round_max",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= 4160749568 → val(tlsf_round(s)) <= 4160749568",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_round_bounds"), [s])),
      arw([]),
      strip,
      have("16 <= val(\{r})", @int.asm_arith_tac),
      @tactics.mp_tac(inst(thm("tlsf_class"), [r])),
      arw([]),
      strip,
      have(
        "\{k} <= 134217728",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_exp_le"), ["val(tlsf_fli(\{r}))-4", "27"]),
          ),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @int.asm_arith_tac,
        ]),
      ),
      have(
        "(16 + \{j}) * \{k} <= 31 * \{k}",
        seq([
          @tactics.mp_tac(
            inst(@arith.le_mult_rcancel(), ["16 + \{j}", "31", k]),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_grow_limits",
    "∀ lim : Num, ∀ pages : \{w}, MOD(lim,65536) == 0 && DIV(lim,65536)+val(pages) <= 65536 → lim <= lim+val(pages)*65536 && lim+val(pages)*65536 <= 4294967296 && MOD(lim+val(pages)*65536,65536) == 0",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(@arith.division(), ["(lim : Num)", "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      strip,
      have(
        "(lim : Num) + val((pages : \{w})) * 65536 <= 4294967296",
        @int.asm_arith_tac,
      ),
      have(
        "MOD((lim : Num)+val((pages : \{w}))*65536,65536) == 0",
        seq([rw([@arith.mod_mult_add()]), arw([])]),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_page_result_not_failure",
    "∀ lim : Num, lim <= 4294967296 → !((word(DIV(lim,65536)) : \{w}) == word(4294967295))",
    seq([
      gen,
      @tactics.disch_tac,
      have(
        "DIV((lim : Num),65536) <= 65536",
        seq([
          @tactics.mp_tac(
            inst(@arith.div_mono(), ["(lim : Num)", "4294967296", "65536"]),
          ),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          arw([]),
        ]),
      ),
      rw([@equal.gsym(@words.val_eq()), @words.val_word(), @words.dimindex_32()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
  let shift = "word_jshl((word(DIV((lim : Num),65536)) : \{w}),word(16))"
  let _ = lemma(
    "tlsf_memory_byte_word",
    "∀ lim : Num, MOD(lim,65536) == 0 → \{shift} == word(lim)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(inst(@arith.division(), ["(lim : Num)", "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      strip,
      have("DIV((lim : Num),65536) * 65536 == lim", @int.asm_arith_tac),
      rw([
        @words.word_jshl(),
        @words.word_shl_word(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([@arith.mult_sym()]),
    ]),
  )
  let diff = "word_sub((word((lim : Num)) : \{w}),(m : \{w}))"
  let _ = lemma(
    "tlsf_limit_sub_value",
    "∀ lim : Num, ∀ m : \{w}, lim <= 4294967296 && 0 < val(m) && val(m) <= lim → val(\{diff}) == lim-val(m)",
    seq([
      gen,
      strip,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(lim : Num) < 4294967296")),
        @list.List([
          seq([
            rw([
              @words.val_word_sub_cases(),
              @words.val_word(),
              @words.dimindex_32(),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @simp.asm_simp_tac(ths([@arith.mod_lt()])),
            arw([]),
            @int.asm_arith_tac,
          ]),
          seq([
            have("(lim : Num) == 4294967296", @int.asm_arith_tac),
            arw([]),
            rw([
              @words.val_word_sub_cases(),
              @words.val_word(),
              @words.dimindex_32(),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @simp.asm_simp_tac(ths([])),
            @int.asm_arith_tac,
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_capacity_value",
    "∀ lim : Num, ∀ m : \{w}, lim <= 4294967296 && 0 < val(m) && val(m)+24 <= lim → val(tlsf_capacity_at(lim,m)) == lim-val(m)-8",
    seq([
      gen,
      strip,
      have(
        "val(\{diff}) == (lim : Num)-val((m : \{w}))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_limit_sub_value"), ["(lim : Num)", "(m : \{w})"]),
          ),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      rw([thm("tlsf_capacity_at")]),
      @simp.once_rewrite_tac(ths([@words.val_word_sub_cases()])),
      rw([@words.val_word(), @words.dimindex_32()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      @simp.asm_simp_tac(ths([])),
      @int.asm_arith_tac,
    ]),
  )
  let cap = "tlsf_capacity_at((lim : Num),(m : \{w}))"
  let _ = lemma(
    "tlsf_capacity_fields",
    "∀ lim : Num, ∀ m : \{w}, lim <= 4294967296 && 0 < val(m) && val(m)+24 <= lim && MOD(lim,8) == 0 && MOD(val(m),8) == 0 → 16 <= val(\{cap}) && MOD(val(\{cap}),8) == 0 && tlsf_size(\{cap}) == \{cap} && val(m)+8+val(\{cap}) == lim",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_capacity_value"), ["(lim : Num)", "(m : \{w})"]),
      ),
      arw([]),
      @tactics.disch_tac,
      have(
        "MOD(val(\{cap}),8) == 0",
        seq([
          arw([]),
          @tactics.match_mp_tac(thm("tlsf_aligned_sub")),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      have(
        "MOD(val(\{cap}),4) == 0",
        seq([@tactics.match_mp_tac(thm("tlsf_mod8_4")), arw([])]),
      ),
      arw([thm("tlsf_size_clean")]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_page_aligned8",
    "∀ lim : Num, MOD(lim,65536) == 0 → MOD(lim,8) == 0",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(@arith.mod_mod_exp_min(), ["(lim : Num)", "2", "16", "3"]),
      ),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}
