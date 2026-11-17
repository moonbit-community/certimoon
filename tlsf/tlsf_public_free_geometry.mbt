// The public guard and tag test follow from physical and small-slot geometry.

///|
fn prove_tlsf_public_free_geometry() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let m = "(m : " + w + ")"
  let hdr = a[4] + "(" + m + ")"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_public_free_unpayload",
    "∀ m : " + w + ", word_sub(word_add(m,word(8)),word(8)) == m",
    () => @words.word_arith_tac,
  )
  let _ = lemma(
    "tlsf_public_free_tag_mask",
    "∀ h : " +
    w +
    ", word_and(tlsf_size(h),word(4)) == word_and(h,word(4)) && word_and(word_and(tlsf_size(h),word(7)),word(4)) == word_and(tlsf_size(h),word(4))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_size"), thm("tlsf_and_assoc")]),
        @tactics.conv_tac(@words.word_reduce_conv),
        rw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_public_free_large_tag",
    "∀ h : " +
    w +
    ", MOD(val(tlsf_size(h)),8) == 0 → word_and(h,word(4)) == word(0)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have(
          "word_and(tlsf_size((h : " + w + ")),word(7)) == word(0)",
          seq([
            rw([@equal.gsym(@words.val_eq()), @words.val_word_0()]),
            arw([
              @equal.conv_rule(
                @calc_num.num_reduce_conv,
                inst(@words.val_word_and_mask_word(), [
                  "tlsf_size((h : " + w + "))",
                  "3",
                ]),
              ),
            ]),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_public_free_tag_mask"), ["(h : " + w + ")"]),
        ),
        arw([@words.word_and_0()]),
        @tactics.try_tac(seq([strip, arw([])])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_public_free_guard_value",
    "∀ d : " +
    w +
    ", val(d) <= 4294965088 → val(word_add(tlsf_base(d),word(2184))) == val(tlsf_base(d))+2184 && 0 < val(word_add(tlsf_base(d),word(2184)))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(inst(thm("tlsf_initialize_base_bounds"), [a[0]])),
        arw([]),
        strip,
        free_have(
          "val(word_add(tlsf_base(" +
          a[0] +
          "),word(2184))) == val(tlsf_base(" +
          a[0] +
          "))+2184",
          seq([@logic.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let block = "tlsf_block_ok(val(" +
    m +
    ")," +
    a[1] +
    "," +
    m +
    "," +
    a[4] +
    ")"
  let _ = lemma(
    "tlsf_public_free_block_geometry",
    page_quantify(page_model_variables() + [("m", w)]) +
    physical +
    " && MEM(" +
    m +
    "," +
    a[3] +
    ") → " +
    block +
    " && " +
    a[1] +
    " <= 4294967296 && tlsf_origin(" +
    a[0] +
    ") <= val(" +
    m +
    ") && val(" +
    a[0] +
    ") <= 4294965088 && word_and(" +
    hdr +
    ",word(4)) == word(0)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_physical_ok")]),
        strip,
        free_have(
          block,
          seq([
            @logic.match_mp_tac(
              inst(thm("tlsf_layout_members"), [
                a[3],
                "(word(0) : " + w + ")",
                "tlsf_origin(" + a[0] + ")",
                a[1],
                a[2],
                a[4],
                m,
              ]),
            ),
            arw([]),
          ]),
        ),
        free_have(
          "tlsf_origin(" + a[0] + ") <= val(" + m + ")",
          seq([
            @logic.match_mp_tac(
              inst(thm("tlsf_layout_lower"), [
                a[3],
                "(word(0) : " + w + ")",
                "tlsf_origin(" + a[0] + ")",
                a[1],
                a[2],
                a[4],
                m,
              ]),
            ),
            arw([]),
          ]),
        ),
        arw([]),
        @logic.match_mp_tac(thm("tlsf_public_free_large_tag")),
        @tactics.undisch_tac(tm(block)),
        rw([thm("tlsf_block_ok")]),
        small_meson(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_public_free_pointer_guard",
    "∀ d : " +
    w +
    ", ∀ m : " +
    w +
    ", val(d) <= 4294965088 && tlsf_origin(d) <= val(m) && val(m)+8 < 4294967296 → val(word_add(m,word(8))) == val(m)+8 && !word_ult(word_add(m,word(8)),word_add(tlsf_base(d),word(2184)))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "val(word_add(" + m + ",word(8))) == val(" + m + ")+8",
          seq([@logic.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        @tactics.mp_tac(inst(thm("tlsf_public_free_guard_value"), [a[0]])),
        arw([]),
        strip,
        arw([@words.word_ult_v1()]),
        @tactics.undisch_tac(tm("tlsf_origin(" + a[0] + ") <= val(" + m + ")")),
        rw([thm("tlsf_origin")]),
        @int.asm_arith_tac,
      ])
    },
  )
}
