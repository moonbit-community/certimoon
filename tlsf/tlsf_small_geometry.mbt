// Slot placement and the exact partition of each page's usable area.

///|
fn prove_tlsf_small_geometry() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_slots_member",
    "∀ n : Num, ∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, MEM(b,tlsf_small_slots(p,s,n)) == (∃ i : Num, i < n && b == tlsf_small_slot(p,s,i))",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_small_slots"),
        @lists.mem(),
        @arith.lt(),
        @lists.mem_append(),
      ]),
      gen,
      arw([]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_slots_length",
    "∀ n : Num, ∀ p : \{w}, ∀ s : Num, LENGTH(tlsf_small_slots(p,s,n)) == n",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_small_slots"),
        @lists.length(),
        @lists.length_append(),
        @arith.add_clauses(),
      ]),
      gen,
      arw([]),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_capacity",
    "∀ s : Num, 8 <= s && s <= 256 → 4 <= tlsf_small_total(s) && tlsf_small_total(s) <= 66 && (8+s)*tlsf_small_total(s) <= 1056",
    seq([
      gen,
      strip,
      rw([thm("tlsf_small_total")]),
      @tactics.mp_tac(inst(@arith.div_mul_le(), ["1056", "8+(s : Num)"])),
      @tactics.mp_tac(inst(@arith.le_ldiv_eq(), ["8+(s : Num)", "1056", "66"])),
      @tactics.mp_tac(inst(@arith.le_rdiv_eq(), ["8+(s : Num)", "1056", "4"])),
      @int.asm_arith_tac,
    ]),
  )
  let facts = "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let _ = lemma(
    "tlsf_small_slot_bounds",
    "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ i : Num, \{facts} && i < tlsf_small_total(s) → val(tlsf_small_slot(p,s,i)) == val(p)+32+(8+s)*i && val(p)+32 <= val(tlsf_small_slot(p,s,i)) && val(tlsf_small_slot(p,s,i))+8+s <= val(p)+8+cap && !(tlsf_small_slot(p,s,i) == word(0))",
    seq([
      gen,
      rw([thm("tlsf_small_page_ok")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_small_capacity"), ["(s : Num)"])),
      arw([]),
      strip,
      free_have(
        "(8+(s : Num))*((i : Num)+1) <= (8+s)*tlsf_small_total(s)",
        seq([@tactics.match_mp_tac(@arith.le_mult2()), @int.asm_arith_tac]),
      ),
      free_have(
        "val((p : \{w}))+32+(8+(s : Num))*(i : Num) < 4294967296",
        @int.asm_arith_tac,
      ),
      free_have(
        "val(tlsf_small_slot((p : \{w}),(s : Num),(i : Num))) == val(p)+32+(8+s)*i",
        seq([
          rw([thm("tlsf_small_slot"), @words.val_word(), @words.dimindex_32()]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @tactics.match_mp_tac(@arith.mod_lt()),
          arw([]),
        ]),
      ),
      arw([]),
      free_have(
        "!(tlsf_small_slot((p : \{w}),(s : Num),(i : Num)) == word(0))",
        seq([
          rw([@equal.gsym(@words.val_eq()), @words.val_word_0()]),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}

///|
fn prove_tlsf_small_slot_separation() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let args = [
    "(lim : Num)",
    "(p : \{w})",
    "(cap : Num)",
    "(s : Num)",
    "(loc : \{lw})",
    "(cached : \{lw})",
    "(live : \{lw})",
  ]
  let vars = "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ i : Num, ∀ j : Num"
  let ok = "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let si = "tlsf_small_slot((p : \{w}),(s : Num),(i : Num))"
  let sj = "tlsf_small_slot((p : \{w}),(s : Num),(j : Num))"
  let expose = seq([
    @tactics.mp_tac(inst(thm("tlsf_small_slot_bounds"), args + ["(i : Num)"])),
    arw([]),
    strip,
    @tactics.mp_tac(inst(thm("tlsf_small_slot_bounds"), args + ["(j : Num)"])),
    arw([]),
    strip,
  ])
  let _ = lemma(
    "tlsf_small_slot_injective",
    "\{vars}, \{ok} && i < tlsf_small_total(s) && j < tlsf_small_total(s) → ((\{si} == \{sj}) == (i == j))",
    seq([
      gen,
      strip,
      expose,
      rw([@equal.gsym(@words.val_eq())]),
      arw([]),
      rw([@arith.eq_add_lcancel(), @arith.eq_mult_lcancel()]),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_slots_disjoint",
    "\{vars}, \{ok} && i < j && j < tlsf_small_total(s) → val(\{si})+8+s <= val(\{sj})",
    seq([
      gen,
      strip,
      free_have("(i : Num) < tlsf_small_total((s : Num))", @int.asm_arith_tac),
      expose,
      @tactics.mp_tac(
        inst(@arith.le_mult2(), [
          "8+(s : Num)", "8+(s : Num)", "(i : Num)+1", "(j : Num)",
        ]),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}
