// Natural-number geometry for an unpublished page, including the memory32
// endpoint. Compiled arithmetic is related to these non-wrapping addresses.

///|
fn prove_tlsf_page_allocate_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_page_allocate_total_word",
    "∀ s : \{w}, 8 <= val(s) && val(s) <= 256 → !(word_add(s,word(8)) == word(0)) && word_udiv(word(1056),word_add(s,word(8))) == word(tlsf_small_total(val(s)))",
    seq([
      gen,
      strip,
      free_have(
        "val(word_add((s : \{w}),word(8))) == val(s)+8",
        seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
      ),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            rw([@equal.gsym(@words.val_eq()), @words.val_word_0()]),
            arw([]),
            @int.asm_arith_tac,
          ]),
          seq([
            rw([
              @words.word_udiv(),
              @words.modular(),
              @words.val_word(),
              @words.dimindex_32(),
              thm("tlsf_small_total"),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            arw([@arith.add_sym()]),
          ]),
        ]),
      ),
    ]),
  )
  let geom = "tlsf_page_allocate_geometry((p : \{w}),(cap : Num),(s : Num))"
  let _ = lemma(
    "tlsf_page_allocate_bounds",
    "∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ k : Num, \{geom} && k < tlsf_small_total(s) → val(tlsf_small_slot(p,s,k)) == val(p)+32+(8+s)*k && val(tlsf_small_slot(p,s,k))+8+s <= val(p)+8+cap && val(p)+32+(8+s)*k < 4294967296",
    seq([
      gen,
      rw([thm("tlsf_page_allocate_geometry")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_small_capacity"), ["(s : Num)"])),
      arw([]),
      strip,
      free_have(
        "(8+(s : Num))*((k : Num)+1) <= (8+s)*tlsf_small_total(s)",
        seq([@tactics.match_mp_tac(@arith.le_mult2()), @int.asm_arith_tac]),
      ),
      free_have(
        "val((p : \{w}))+32+(8+(s : Num))*(k : Num) < 4294967296",
        @int.asm_arith_tac,
      ),
      rw([thm("tlsf_small_slot"), @words.val_word(), @words.dimindex_32()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_page_allocate_slot_word",
    "∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ k : Num, tlsf_page_allocate_geometry(p,cap,val(s)) && k < tlsf_small_total(val(s)) → word_add(word_add(p,word(32)),word_mul(word(k),word_add(s,word(8)))) == tlsf_small_slot(p,val(s),k)",
    seq([
      gen,
      strip,
      rw([
        thm("tlsf_small_slot"),
        @words.word_add_v1(),
        @words.word_mul_v1(),
        @words.word_val(),
      ]),
      g => @tactics.accept_tac(@words.word_rule(g.1))(g),
    ]),
  )
  let _ = lemma(
    "tlsf_page_allocate_head_suc",
    "∀ p : \{w}, ∀ s : Num, ∀ k : Num, tlsf_page_allocate_head(p,s,SUC(k)) == tlsf_small_slot(p,s,k)",
    rw([thm("tlsf_page_allocate_head"), @nums.not_suc(), @arith.suc_sub1()]),
  )
}

///|
fn prove_tlsf_page_allocate_compare() -> Unit raise {
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_allocate_compare",
    "∀ k : Num, ∀ n : Num, k <= n && n <= 66 → word_ult((word(k) : \{w32}),word(n)) == (k < n)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_have(
        "(k : Num) < 4294967296 && (n : Num) < 4294967296", @int.asm_arith_tac,
      ),
      rw([
        @words.word_ult(),
        @words.relational2(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
    ]),
  )
}
