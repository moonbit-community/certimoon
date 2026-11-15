///|
fn prove_tlsf_ensure_metadata() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let base = "tlsf_base((d : \{w}))"
  let slot = "tlsf_top_cell((d : \{w}))"
  let _ = lemma(
    "tlsf_ensure_metadata_address",
    "∀ d : \{w}, val(d) <= 4294965088 → val(\{slot}) == val(\{base})+1908",
    seq([
      gen,
      @tactics.disch_tac,
      have(
        "val(word_add((d : \{w}),word(15))) == val(d)+15",
        seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(
        inst(@bool.conjuncts_rule(@words.val_word_and_le()).to_array()[0], [
          "word_add((d : \{w}),word(15))",
          "(word(4294967280) : \{w})",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      rw([thm("tlsf_top_cell")]),
      @tactics.match_mp_tac(thm("val_add_small")),
      rw([thm("tlsf_base")]),
      @int.asm_arith_tac,
    ]),
  )
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),(m : \{w}),APPEND((ys : \{lw}),[m]),(hd : \{ht}))"
  let _ = lemma(
    "tlsf_ensure_metadata_guards",
    "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}, \{old} → !word_ugt(d,word(4294965088)) && !word_uge(word_jushr(\{slot},word(16)),(word(DIV(lim,65536)) : \{w}))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_ensure_top_facts"), [
          "(ys : \{lw})",
          "(d : \{w})",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      have(
        "val((d : \{w})) <= 4294965088 && tlsf_layout((word(0) : \{w}),tlsf_origin(d),(lim : Num),(m : \{w}),APPEND((ys : \{lw}),[m]),(hd : \{ht}))",
        seq([
          @tactics.undisch_tac(tm(old)),
          rw([thm("tlsf_physical_ok")]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "/\\" {
          @tactics.strip_assume_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      @tactics.mp_tac(
        inst(thm("tlsf_layout_lower"), [
          "APPEND((ys : \{lw}),[(m : \{w})])",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
          "(m : \{w})",
        ]),
      ),
      arw([@lists.mem_append(), @lists.mem()]),
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_ensure_metadata_address"), ["(d : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      have(
        "val(\{slot}) < (lim : Num)",
        seq([
          @tactics.undisch_tac(tm("tlsf_origin((d : \{w})) <= val((m : \{w}))")),
          rw([thm("tlsf_origin")]),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.mp_tac(inst(@arith.division(), ["val(\{slot})", "65536"])),
      @tactics.mp_tac(inst(@arith.division(), ["(lim : Num)", "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      strip,
      have(
        "DIV(val(\{slot}),65536) < DIV((lim : Num),65536)",
        @int.asm_arith_tac,
      ),
      have(
        "DIV((lim : Num),65536) <= 65536",
        seq([
          @tactics.mp_tac(
            inst(@arith.div_mono(), ["(lim : Num)", "4294967296", "65536"]),
          ),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          arw([]),
        ]),
      ),
      have("DIV((lim : Num),65536) < 4294967296", @int.asm_arith_tac),
      rw([
        @words.word_ugt_v1(),
        @words.word_uge_v1(),
        thm("tlsf_shr16_value"),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
}
