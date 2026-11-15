///|
fn prove_tlsf_free_merge_flags() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let split = lemma(
    "tlsf_free_flags_split",
    "∀ h : \{w}, word_and(h,word(3)) == word_or(word_and(h,word(1)),word_and(h,word(2)))",
    seq([
      gen,
      rw([
        @equal.sym(
          @words.word_reduce_conv(tm("(word_or(word(1),word(2)) : \{w})")),
        ),
      ]),
      g => @tactics.accept_tac(@words.word_bitwise_rule(g.1))(g),
    ]),
  )
  let _ = lemma(
    "tlsf_free_low_flags",
    "∀ h : \{w}, !tlsf_used(h) && !tlsf_last(h) → word_and(h,word(3)) == word(0)",
    seq([
      gen,
      rw([thm("tlsf_used"), thm("tlsf_last")]),
      strip,
      arw([split, @words.word_or_0()]),
    ]),
  )
  let z = "tlsf_merge_size((hm : \{w}),(hr : \{w}))"
  let raw = "word_or(word_and((hm : \{w}),word(3)),\{z})"
  for last in [true, false] {
    let out = if last {
      "word_or(word_and(\{raw},word(4294967293)),word(2))"
    } else {
      raw
    }
    let cond = if last {
      "tlsf_last((hr : \{w}))"
    } else {
      "!tlsf_last((hr : \{w}))"
    }
    let bit = if last { "word(2)" } else { "word(0)" }
    let _ = lemma(
      if last {
        "tlsf_free_merge_store_last"
      } else {
        "tlsf_free_merge_store_next"
      },
      "∀ hm : \{w}, ∀ hr : \{w}, !tlsf_used(hm) && !tlsf_last(hm) && tlsf_size(\{z}) == \{z} && \{cond} → \{out} == tlsf_merge_header(hm,hr)",
      seq([
        gen,
        strip,
        free_have(
          "word_and((hm : \{w}),word(3)) == word(0)",
          seq([@tactics.match_mp_tac(thm("tlsf_free_low_flags")), arw([])]),
        ),
        free_have(
          "word_and((hr : \{w}),word(2)) == (\{bit} : \{w})",
          seq([
            @tactics.mp_tac(inst(thm("tlsf_last_mask_cases"), ["(hr : \{w})"])),
            @tactics.undisch_tac(tm(cond)),
            rw([thm("tlsf_last")]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        @tactics.mp_tac(inst(thm("tlsf_clean_low_bits"), [z])),
        arw([]),
        strip,
        arw([thm("tlsf_merge_header"), @words.word_or_0()]),
      ]),
    )
  }
}
