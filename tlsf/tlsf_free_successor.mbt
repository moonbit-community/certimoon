///|
fn prove_tlsf_free_successor() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let z = "tlsf_size((h : \{w}))"
  let p = "word_add(word_add((m : \{w}),\{z}),word(8))"
  let rb = @equal.conv_rule(
    @calc_num.num_reduce_conv,
    @simp.rewrite_rule(ths([@words.dimindex_32()]))(
      @bool.ispec(tm("(r : \{w})"), @words.val_bound()),
    ),
  )
  let _ = lemma(
    "tlsf_free_successor",
    "∀ m : \{w}, ∀ r : \{w}, ∀ h : \{w}, val(r) == val(m)+8+val(\{z}) → r == \{p}",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.assume_tac(rb),
        free_have(
          "val(word_add((m : \{w}),\{z})) == val(m)+val(\{z})",
          seq([
            @tactics.match_mp_tac(thm("tlsf_val_add_exact")),
            @int.asm_arith_tac,
          ]),
        ),
        free_have(
          "val(\{p}) == val((r : \{w}))",
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_val_add_exact"), [
                "word_add((m : \{w}),\{z})",
                "(word(8) : \{w})",
              ]),
            ),
            arw([]),
            @tactics.conv_tac(@words.word_reduce_conv),
            @int.asm_arith_tac,
          ]),
        ),
        arw([@equal.gsym(@words.val_eq())]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_successor_prev",
    "∀ m : \{w}, ∀ r : \{w}, ∀ h : \{w}, r == \{p} → word_add(word_add(m,\{z}),word(12)) == word_add(r,word(4))",
    () => {
      seq([
        gen,
        strip,
        arw([]),
        g => @tactics.accept_tac(@words.word_rule(g.1))(g),
      ])
    },
  )
}
