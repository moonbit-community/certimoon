///|
fn prove_tlsf_ensure_bytes() -> Unit raise {
  let b = "Word[8]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let rep = lemma(
    "tlsf_replicate_add",
    "∀ n : Num, ∀ k : Num, ∀ x : \{b}, REPLICATE(n+k,x) == APPEND(REPLICATE(n,x),REPLICATE(k,x))",
    () => {
      seq([
        @nums.induct_tac,
        rw([@lists.replicate(), @lists.append(), @arith.add_clauses()]),
        gen,
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_zeros_bytes",
    "∀ a : Num, ∀ n : Num, ∀ h : \{heap}, pts(a,REPLICATE(n,(word(0) : \{b})),h) → tlsf_bytes(a,n,h)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_bytes")]),
        @tactics.exists_tac(tm("REPLICATE((n : Num),(word(0) : \{b}))")),
        arw([@lists.length_replicate()]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_le_zero_bytes",
    "∀ n : Num, le_bytes(n,0) == REPLICATE(n,(word(0) : \{b}))",
    () => {
      seq([
        @nums.induct_tac,
        rw([@wasm.thm("le_bytes"), @lists.replicate()]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_zeros_word",
    "∀ a : Num, ∀ n : Num, 4 <= n → pts(a,REPLICATE(n,(word(0) : \{b}))) == star(pts(a,serialise_i32((word(0) : \{w32}))),pts(a+4,REPLICATE(n-4,(word(0) : \{b}))))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        have("4+((n : Num)-4) == n", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("pts_split"), [
            "(a : Num)",
            "REPLICATE(4,(word(0) : \{b}))",
            "REPLICATE((n : Num)-4,(word(0) : \{b}))",
          ]),
        ),
        rw([@equal.gsym(rep), @lists.length_replicate()]),
        arw([]),
        rw([
          @wasm.thm("serialise_i32"),
          @words.val_word_0(),
          thm("tlsf_le_zero_bytes"),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
      ])
    },
  )
  let _ = lemma(
    "tlsf_grown_bytes",
    "∀ a : Num, ∀ n : Num, ∀ k : Num, ∀ h : \{heap}, star(tlsf_bytes(a,n),pts(a+n,REPLICATE(k,(word(0) : \{b}))),h) → tlsf_bytes(a,n+k,h)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bytes_split"), thm("tlsf_bytes")] + lift_rws()),
        strip,
        @tactics.exists_tac(tm("(bs : List[\{b}])")),
        @tactics.exists_tac(tm("REPLICATE((k : Num),(word(0) : \{b}))")),
        arw([@lists.length_replicate()] + lift_rws()),
      ])
    },
  )
}
