///|
fn prove_tlsf_ensure_pages() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_shr16_value",
    "∀ x : \{w}, val(word_jushr(x,word(16))) == DIV(val(x),65536)",
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
  let _ = lemma(
    "tlsf_ceil_pages",
    "∀ x : Num, x <= DIV(x+65535,65536)*65536 && DIV(x+65535,65536)*65536 < x+65536",
    seq([
      gen,
      @tactics.mp_tac(inst(@arith.division(), ["(x : Num)+65535", "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @int.arith_tac,
    ]),
  )
  let req = "tlsf_ensure_expected((s : \{w}))"
  let _ = lemma(
    "tlsf_ensure_expected_bounds",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= 4160749568 → val(s) <= val(\{req}) && 16 <= val(\{req}) && val(\{req}) <= 4160749568",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_align_bounds"), ["(s : \{w})"])),
      arw([]),
      strip,
      have("16 <= val(tlsf_align((s : \{w})))", @int.asm_arith_tac),
      @tactics.mp_tac(
        inst(thm("tlsf_round_bounds"), ["tlsf_align((s : \{w}))"]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_round_max"), ["tlsf_align((s : \{w}))"])),
      arw([thm("tlsf_ensure_expected")]),
      @int.asm_arith_tac,
    ]),
  )
  let used = "word_jushr(word_add((e : \{w}),word(65543)),word(16))"
  let _ = lemma(
    "tlsf_used_pages_value",
    "∀ e : \{w}, val(e) <= 4160749568 → val(\{used}) == DIV(val(e)+65543,65536)",
    seq([
      gen,
      @tactics.disch_tac,
      rw([thm("tlsf_shr16_value")]),
      have(
        "val(word_add((e : \{w}),word(65543))) == val(e)+65543",
        seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
      ),
      arw([]),
    ]),
  )
  let free = "word_jushr(word_add(word_sub((e : \{w}),(z : \{w})),word(65535)),word(16))"
  let _ = lemma(
    "tlsf_free_pages_value",
    "∀ e : \{w}, ∀ z : \{w}, val(e) <= 4160749568 && val(z) < val(e) → val(\{free}) == DIV(val(e)-val(z)+65535,65536)",
    seq([
      gen,
      strip,
      have(
        "val(word_sub((e : \{w}),(z : \{w}))) == val(e)-val(z)",
        seq([
          rw([@words.val_word_sub_cases()]),
          @simp.asm_simp_tac(ths([])),
          @int.asm_arith_tac,
        ]),
      ),
      have(
        "val(word_add(word_sub((e : \{w}),(z : \{w})),word(65535))) == val(e)-val(z)+65535",
        seq([
          @tactics.mp_tac(
            inst(thm("val_add_small"), [
              "word_sub((e : \{w}),(z : \{w}))",
              "65535",
            ]),
          ),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      rw([thm("tlsf_shr16_value")]),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_used_pages_fit",
    "∀ e : \{w}, 16 <= val(e) && val(e) <= 4160749568 → 0 < val(\{used}) && val(e)+8 <= val(\{used})*65536",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_used_pages_value"), ["(e : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_ceil_pages"), ["val((e : \{w}))+8"])),
      arw([arith("val((e : \{w}))+8+65535 == val(e)+65543")]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_free_pages_fit",
    "∀ e : \{w}, ∀ z : \{w}, val(e) <= 4160749568 → val(e) <= val(z)+val(\{free})*65536",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("val((z : \{w})) < val((e : \{w}))")),
        @list.List([
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_free_pages_value"), ["(e : \{w})", "(z : \{w})"]),
            ),
            arw([]),
            @tactics.disch_tac,
            @tactics.mp_tac(
              inst(thm("tlsf_ceil_pages"), ["val((e : \{w}))-val((z : \{w}))"]),
            ),
            @int.asm_arith_tac,
          ]),
          @int.asm_arith_tac,
        ]),
      ),
    ]),
  )
}
