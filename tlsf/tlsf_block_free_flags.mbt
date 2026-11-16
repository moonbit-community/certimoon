///|
fn prove_tlsf_block_free_flags() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_usage_flag",
    "∀ u : Num, ∀ total : Num, u <= 66 && total <= 66 → (wasm_bool((word(u) : \{w}) == word(total)) : \{w}) == (if u == total { word(1) } else { word(0) })",
    seq([
      gen,
      strip,
      g => {
        @tactics.assume_tac(
          block_under(
            inst(thm("tlsf_small_word_eq"), ["(u : Num)", "(total : Num)"]),
            g,
          ),
        )(g)
      },
      arw([@wasm.thm("wasm_bool")]),
    ]),
  )
  let _ = lemma(
    "tlsf_small_usage_one_flag",
    "∀ u : Num, u <= 66 → (wasm_bool((word(u) : \{w}) == word(1)) : \{w}) == (if u == 1 { word(1) } else { word(0) })",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("tlsf_small_usage_flag")),
      arw([]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
}
