///|
fn prove_tlsf_malloc_cached_frames() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let n = malloc_cached_args(a, p, b, bs, k)
  let rest = a.copy()
  rest[8] = "tlsf_small_remove(" + p + "," + a[8] + ")"
  let nr = n.copy()
  nr[8] = rest[8]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_malloc_cached_pages_rest",
    page_quantify(
      page_model_variables() + [("p", w), ("b", w), ("bs", lw), ("k", "Num")],
    ) +
    block_pages(nr) +
    " == " +
    block_pages(rest),
    seq([
      gen,
      rw([thm("tlsf_small_pages_hlist")]),
      @tactics.match_mp_tac(thm("tlsf_small_hlist_cong")),
      @tactics.x_gen_tac(tm("(q : " + w + ")")),
      @tactics.disch_tac,
      free_have(
        "!((q : " + w + ") == " + p + ")",
        small_meson(ths([thm("tlsf_small_remove_member")])),
      ),
      arw([thm("tlsf_small_put")]),
    ]),
  )
  let _ = lemma(
    "tlsf_malloc_small_shift",
    "∀ k : Num, k < 33 → word_jshl((word(k) : " +
    w +
    "),word(3)) == word(8*k)",
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
}
