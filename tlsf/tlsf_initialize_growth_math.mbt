///|
fn prove_tlsf_initialize_growth_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let req = "tlsf_initialize_required(\{d})"
  let pages = "tlsf_initialize_pages(\{d})"
  let old = "(word(DIV(\{lim},65536)) : \{w})"
  let _ = lemma(
    "tlsf_initialize_old_pages",
    "∀ lim : Num, lim <= 4294967296 → val(\{old}) == DIV(lim,65536) && DIV(lim,65536) <= 65536",
    seq([
      gen,
      @tactics.disch_tac,
      free_have(
        "DIV(\{lim},65536) <= 65536",
        seq([
          @tactics.mp_tac(inst(@arith.div_mono(), [lim, "4294967296", "65536"])),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @int.asm_arith_tac,
        ]),
      ),
      free_have("DIV(\{lim},65536) < 4294967296", @int.asm_arith_tac),
      rw([@words.val_word(), @words.dimindex_32()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
  let cond = "word_ugt(\{req},\{old})"
  let _ = lemma(
    "tlsf_initialize_growth_test",
    "∀ d : \{w}, ∀ lim : Num, tlsf_initialize_valid(d,lim) → (\{cond} == (lim < \{pages}*65536))",
    seq([
      gen,
      rw([thm("tlsf_initialize_valid")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_old_pages"), [lim])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_required_value"), [d])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(@arith.division(), [lim, "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      strip,
      arw([@words.word_ugt_v1()]),
      @int.asm_arith_tac,
    ]),
  )
  let delta = "word_sub(\{req},\{old})"
  let _ = lemma(
    "tlsf_initialize_growth_delta",
    "∀ d : \{w}, ∀ lim : Num, tlsf_initialize_valid(d,lim) && \{cond} → val(\{delta}) == \{pages}-DIV(lim,65536) && lim+val(\{delta})*65536 == \{pages}*65536 && DIV(lim,65536)+val(\{delta}) <= 65536",
    seq([
      gen,
      strip,
      @tactics.undisch_tac(tm("tlsf_initialize_valid(\{d},\{lim})")),
      rw([thm("tlsf_initialize_valid")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_old_pages"), [lim])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_required_value"), [d])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_page_bounds"), [d])),
      arw([]),
      strip,
      free_have(
        "DIV(\{lim},65536) < \{pages}",
        seq([
          @tactics.undisch_tac(tm(cond)),
          arw([@words.word_ugt_v1()]),
          @int.asm_arith_tac,
        ]),
      ),
      free_have(
        "val(\{delta}) == \{pages}-DIV(\{lim},65536)",
        seq([arw([@words.val_word_sub_cases()]), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(inst(@arith.division(), [lim, "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_limit_cases",
    "∀ d : \{w}, ∀ lim : Num, tlsf_initialize_valid(d,lim) → ((\{cond} → tlsf_initialize_limit(d,lim) == \{pages}*65536) && (!\{cond} → tlsf_initialize_limit(d,lim) == lim))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_initialize_growth_test"), [d, lim])),
      arw([]),
      @tactics.disch_tac,
      arw([thm("tlsf_initialize_limit"), @arith.max()]),
      @class.cond_cases_tac,
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}
