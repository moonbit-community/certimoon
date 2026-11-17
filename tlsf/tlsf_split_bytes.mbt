///|
fn prove_tlsf_split_bytes() -> Unit raise {
  let b = "Word[8]"
  let lb = "List[\{b}]"
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let bbound = @equal.conv_rule(
    @calc_num.num_reduce_conv,
    @simp.rewrite_rule(ths([@words.dimindex_8()]))(
      @bool.ispec(tm("(h : \{b})"), @words.val_bound()),
    ),
  )
  let div_add = @simp.rewrite_rule(ths([]))(
    @equal.conv_rule(
      @calc_num.num_reduce_conv,
      inst(@bool.conjuncts_rule(@arith.div_mult_add()).to_array()[3], [
        "(n : Num)",
        "val((h : \{b}))",
        "256",
      ]),
    ),
  )
  let div256 = lemma(
    "tlsf_byte_div",
    "∀ h : \{b}, ∀ n : Num, DIV(val(h) + 256 * n, 256) == n",
    () => {
      seq([
        gen,
        @tactics.mp_tac(bbound),
        @tactics.disch_tac,
        have(
          "DIV(val((h : \{b})), 256) == 0",
          seq([@tactics.match_mp_tac(@arith.div_lt()), arw([])]),
        ),
        rw([div_add]),
        arw([@arith.add_clauses()]),
      ])
    },
  )
  let inverse = lemma(
    "tlsf_le_bytes_num",
    "∀ bs : \{lb}, le_bytes(LENGTH(bs), num_of_bytes(bs)) == bs",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([@lists.length(), @wasm.thm("le_bytes"), @wasm.thm("num_of_bytes")]),
        rw([div256]),
        @tactics.conv_tac(
          @simp.pure_once_rewrite_conv(
            ths([@equal.gsym(@words.word_mod_size())]),
          ),
        ),
        rw([@words.dimindex_8()]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        rw([@arith.mod_mult_add()]),
        @simp.asm_simp_tac(ths([@arith.mod_lt(), bbound, @words.word_val()])),
        arw([]),
      ])
    },
  )
  let len = lemma(
    "tlsf_le_bytes_length",
    "∀ k : Num, ∀ n : Num, LENGTH(le_bytes(k, n)) == k",
    () => {
      seq([
        @nums.induct_tac,
        rw([@wasm.thm("le_bytes"), @lists.length()]),
        gen,
        arw([]),
      ])
    },
  )
  let trunc = lemma(
    "tlsf_le_bytes_mod",
    "∀ k : Num, ∀ n : Num, le_bytes(k, MOD(n, EXP(256, k))) == le_bytes(k, n)",
    () => {
      seq([
        gen,
        @tactics.mp_tac(inst(inverse, ["le_bytes((k : Num), (n : Num))"])),
        rw([len, thm("num_of_le_bytes")]),
      ])
    },
  )
  let roundtrip = lemma(
    "tlsf_serialise_deserialise",
    "∀ bs : \{lb}, LENGTH(bs) == 4 → serialise_i32(deserialise_i32(bs)) == bs",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([
          @wasm.thm("serialise_i32"),
          @wasm.thm("deserialise_i32"),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @tactics.mp_tac(inst(trunc, ["4", "num_of_bytes((bs : \{lb}))"])),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @tactics.disch_then(th => @tactics.subst1_tac(th)),
        @tactics.mp_tac(inst(inverse, ["(bs : \{lb})"])),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_bytes_word",
    "∀ a : Num, tlsf_bytes(a, 4) == ((h : \{heap}) => ∃ v : \{w}, pts(a, serialise_i32(v), h))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bytes")]),
        @tactics.abs_tac,
        @tactics.thenl(
          @tactics.eq_tac,
          @list.List([
            seq([
              strip,
              @tactics.exists_tac(tm("deserialise_i32((bs : \{lb}))")),
              @simp.asm_simp_tac(ths([roundtrip])),
            ]),
            seq([
              strip,
              @tactics.exists_tac(tm("serialise_i32((v : \{w}))")),
              arw([thm("serialise_i32_length")]),
            ]),
          ]),
        ),
      ])
    },
  )
  let td = lemma(
    "tlsf_take_drop",
    "∀ xs : \{lb}, ∀ n : Num, APPEND(take(n, xs), drop(n, xs)) == xs",
    () => {
      seq([
        @lists.list_induct_tac,
        @nums.induct_tac,
        rw([@wasm.thm("take"), @wasm.thm("drop"), @lists.append()]),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_bytes_split",
    "∀ a : Num, ∀ n : Num, ∀ k : Num, tlsf_bytes(a, n + k) == star(tlsf_bytes(a, n), tlsf_bytes(a + n, k))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bytes")] + lift_rws()),
        @tactics.abs_tac,
        @tactics.thenl(
          @tactics.eq_tac,
          @list.List([
            seq([
              strip,
              have("(n : Num) <= LENGTH((bs : \{lb}))", @int.asm_arith_tac),
              @tactics.exists_tac(tm("take((n : Num), (bs : \{lb}))")),
              @tactics.exists_tac(tm("drop((n : Num), (bs : \{lb}))")),
              @simp.asm_simp_tac(
                ths([
                  thm("length_take"),
                  thm("length_drop"),
                  arith("(n : Num) + (k : Num) - n == k"),
                ]),
              ),
              @tactics.mp_tac(
                inst(thm("pts_split"), [
                  "(a : Num)",
                  "take((n : Num), (bs : \{lb}))",
                  "drop((n : Num), (bs : \{lb}))",
                ]),
              ),
              @simp.asm_simp_tac(ths([td, thm("length_take")])),
              @tactics.disch_then(th => {
                @tactics.mp_tac(@equal.ap_thm(th, tm("(h : \{heap})")))
              }),
              arw([]),
            ]),
            seq([
              strip,
              @tactics.exists_tac(tm("APPEND((bs : \{lb}), (bs' : \{lb}))")),
              arw([@lists.length_append()]),
              @tactics.mp_tac(
                inst(thm("pts_split"), [
                  "(a : Num)",
                  "(bs : \{lb})",
                  "(bs' : \{lb})",
                ]),
              ),
              arw([]),
              @tactics.disch_then(th => {
                @tactics.mp_tac(@equal.ap_thm(th, tm("(h : \{heap})")))
              }),
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
}
