// Request rounding is done in i32. The small allocation classes are 1..32.

///|
fn prove_tlsf_malloc_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let k = "DIV((n : Num)+7,8)"
  let _ = lemma(
    "tlsf_malloc_small_round",
    "∀ n : Num, 0 < n && n <= 256 → 1 <= " +
    k +
    " && " +
    k +
    " <= 32 && n <= 8*" +
    k +
    " && 8*" +
    k +
    " <= 256 && MOD(8*" +
    k +
    ",8) == 0",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(@arith.division(), ["(n : Num)+7", "8"])),
        @tactics.mp_tac(inst(@arith.div_mono(), ["(n : Num)+7", "263", "8"])),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        strip,
        rw([@arith.mult_sym(), @arith.mod_mult()]),
        @int.asm_arith_tac,
      ])
    },
  )
  let n = "(n : " + w + ")"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let _ = lemma(
    "tlsf_malloc_small_class_word",
    "∀ n : " +
    w +
    ", 0 < val(n) && val(n) <= 256 → " +
    cls +
    " == word(DIV(val(n)+7,8)) && word_jshl(" +
    cls +
    ",word(3)) == word(8*DIV(val(n)+7,8))",
    () => {
      seq([
        gen,
        strip,
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_malloc_small_round"), ["val(" + n + ")"]),
              g,
            ),
          )(g)
        },
        free_have("DIV(val(" + n + ")+7,8) < 4294967296", @int.asm_arith_tac),
        free_have(
          "val(word_add(" + n + ",word(7))) == val(n)+7",
          seq([@logic.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        free_have(
          cls + " == word(DIV(val(" + n + ")+7,8))",
          seq([
            rw([
              @equal.gsym(@words.val_eq()),
              @words.word_jushr(),
              @words.val_word_ushr(),
              @words.val_word(),
              @words.dimindex_32(),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            arw([]),
            @simp.asm_simp_tac(ths([@arith.mod_lt()])),
          ]),
        ),
        arw([
          @words.word_jshl(),
          @words.word_shl(),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @simp.asm_simp_tac(ths([@arith.mod_lt(), @arith.mult_sym()])),
      ])
    },
  )
}

///|
fn prove_tlsf_malloc_cached_partition() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let c = "(cached : " + lw + ")"
  let l = "(live : " + lw + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ p : " +
    w +
    ", ∀ s : Num, ∀ loc : " +
    lw +
    ", ∀ cached : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", "
  let part = "tlsf_small_partition(" +
    p +
    ",(s : Num),(loc : " +
    lw +
    ")," +
    c +
    "," +
    l +
    ")"
  let nc = "tlsf_small_remove(" + b + "," + c + ")"
  let _ = lemma(
    "tlsf_malloc_cached_partition",
    vars +
    part +
    " && MEM(b,cached) → tlsf_small_partition(p,s,loc," +
    nc +
    ",CONS(b,live)) && tlsf_small_used(" +
    nc +
    ",CONS(b,live)) == tlsf_small_used(cached,live) && !MEM(b,live)",
    () => {
      seq([
        gen,
        strip,
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_cached_unique"), [
                p,
                "(s : Num)",
                "(loc : " + lw + ")",
                c,
                l,
                b,
              ]),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.assume_tac(
            block_under(inst(thm("tlsf_small_remove_length_one"), [c, b]), g),
          )(g)
        },
        free_have(
          "tlsf_count(" + b + "," + c + ") == 1 && !MEM(" + b + "," + l + ")",
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_small_partition_counts"), [
                p,
                "(s : Num)",
                "(loc : " + lw + ")",
                c,
                l,
                b,
              ]),
            ),
            arw([@equal.gsym(thm("tlsf_count_zero"))]),
            @class.cond_cases_tac,
            @int.asm_arith_tac,
          ]),
        ),
        split_conjs(),
        rw([
          thm("tlsf_small_partition"),
          thm("tlsf_small_count_append"),
          thm("tlsf_small_count_cons"),
          thm("tlsf_small_remove_count"),
          thm("tlsf_small_used"),
          @lists.length(),
        ]),
        @tactics.undisch_tac(tm(part)),
        rw([
          thm("tlsf_small_partition"),
          thm("tlsf_small_count_append"),
          thm("tlsf_small_used"),
        ]),
        strip,
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(@int.asm_arith_tac),
            solve(arw([])),
            solve(
              seq([
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                @tactics.first_assum(th => {
                  @tactics.mp_tac(@bool.spec(tm("(q : " + w + ")"), th))
                }),
                @tactics.disch_tac,
                @class.asm_cases_tac(tm("(q : " + w + ") == " + b)),
                subst_vars(),
                arw([@theorems.eq_sym_eq()]),
                @int.asm_arith_tac,
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
