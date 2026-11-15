///|
fn prove_tlsf_free_merge_math() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_merge_aligned",
    "∀ a : Num, ∀ b : Num, MOD(a,8) == 0 && MOD(b,8) == 0 → MOD(a+b+8,8) == 0",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(@arith.mod_add_mod(), ["(a : Num)", "(b : Num)", "8"]),
      ),
      arw([]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @tactics.disch_then(th => @tactics.assume_tac(@equal.sym(th))),
      @tactics.mp_tac(
        inst(@arith.mod_add_mod(), ["(a : Num)+(b : Num)", "8", "8"]),
      ),
      arw([]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let a = "(a : \{w})"
  let b = "(b : \{w})"
  let z = "tlsf_merge_size(\{a},\{b})"
  let sum = "val(tlsf_size(\{a}))+val(tlsf_size(\{b}))+8"
  let pre = "\{sum} < 4294967296 && MOD(val(tlsf_size(\{a})),8) == 0 && MOD(val(tlsf_size(\{b})),8) == 0"
  let _ = lemma(
    "tlsf_merge_size_fields",
    "∀ a : \{w}, ∀ b : \{w}, \{pre} → val(\{z}) == \{sum} && MOD(val(\{z}),8) == 0 && tlsf_size(\{z}) == \{z}",
    seq([
      gen,
      strip,
      free_have(
        "val(word_add(tlsf_size(\{a}),tlsf_size(\{b}))) == val(tlsf_size(\{a}))+val(tlsf_size(\{b}))",
        seq([
          @tactics.match_mp_tac(thm("tlsf_val_add_exact")),
          @int.asm_arith_tac,
        ]),
      ),
      free_have(
        "val(\{z}) == \{sum}",
        seq([
          rw([thm("tlsf_merge_size")]),
          @tactics.mp_tac(
            inst(thm("tlsf_val_add_exact"), [
              "word_add(tlsf_size(\{a}),tlsf_size(\{b}))",
              "(word(8) : \{w})",
            ]),
          ),
          arw([]),
          @tactics.conv_tac(@words.word_reduce_conv),
          @int.asm_arith_tac,
        ]),
      ),
      free_have(
        "MOD(val(\{z}),8) == 0",
        seq([arw([]), @tactics.match_mp_tac(thm("tlsf_merge_aligned")), arw([])]),
      ),
      free_have(
        "MOD(val(\{z}),4) == 0",
        seq([@tactics.match_mp_tac(thm("tlsf_mod8_4")), arw([])]),
      ),
      arw([thm("tlsf_size_clean")]),
    ]),
  )
  let _ = lemma(
    "tlsf_merge_header_fields",
    "∀ a : \{w}, ∀ b : \{w}, \{pre} → tlsf_size(tlsf_merge_header(a,b)) == \{z} && !tlsf_used(tlsf_merge_header(a,b)) && (tlsf_last(tlsf_merge_header(a,b)) == tlsf_last(b)) && val(tlsf_size(tlsf_merge_header(a,b))) == \{sum}",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_merge_size_fields"), [a, b])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_remainder_fields"), [z, b])),
      arw([]),
      rw([thm("tlsf_merge_header")]),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}
