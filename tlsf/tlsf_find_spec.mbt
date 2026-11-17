// Connect the compiled search model to physical free blocks and payload sizes.

///|
fn prove_tlsf_find_spec() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let value_mask = @equal.conv_rule(
    @words.word_reduce_conv,
    @equal.conv_rule(
      @calc_num.num_reduce_conv,
      inst(@words.val_word_and_not_mask_word(), [
        "word_add((s : \{w}), word(15))",
        "4",
      ]),
    ),
  )
  let align_val = lemma(
    "tlsf_align_value",
    "∀ s : \{w}, val(s) <= 4160749568 → val(tlsf_align(s)) == 16 * DIV(val(s) + 15, 16)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        have(
          "val(word_add((s : \{w}), word(15))) == val(s) + 15",
          seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        rw([thm("tlsf_align"), value_mask]),
        arw([]),
      ])
    },
  )
  let align_bounds = lemma(
    "tlsf_align_bounds",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= 4160749568 → val(s) <= val(tlsf_align(s)) && val(tlsf_align(s)) <= 4160749568",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(align_val, ["(s : \{w})"])),
        arw([]),
        @tactics.disch_tac,
        @tactics.mp_tac(inst(@arith.division(), ["val((s : \{w})) + 15", "16"])),
        @tactics.mp_tac(
          inst(@arith.div_mono(), [
            "val((s : \{w})) + 15",
            "4160749568 + 15",
            "16",
          ]),
        ),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        have("val((s : \{w})) + 15 <= 4160749583", @int.asm_arith_tac),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let idx = lemma(
    "tlsf_code_index_value",
    "∀ x : \{w}, 16 <= val(x) → val((word_sub(word(27), word(word_clz(x))) : \{w})) == val(tlsf_fli(x)) - 4",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(inst(thm("tlsf_class"), ["(x : \{w})"])),
        arw([]),
        strip,
        rw([thm("tlsf_code_fli")]),
        rw([
          @words.val_word_sub_cases(),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let r = "tlsf_round(tlsf_align((s : \{w})))"
  let size_sound = lemma(
    "tlsf_search_size_sound",
    "∀ s : \{w}, ∀ hd : \{w}, 16 <= val(s) && val(s) <= 4160749568 && 16 <= val(tlsf_size(hd)) && (val(tlsf_search_f(s)) < tlsf_level_of(hd) || (tlsf_level_of(hd) == val(tlsf_search_f(s)) && val(tlsf_search_j(s)) <= tlsf_slot_of(hd))) → val(s) <= val(tlsf_size(hd))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(align_bounds, ["(s : \{w})"])),
        arw([]),
        strip,
        have("16 <= val(tlsf_align((s : \{w})))", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("tlsf_round_bounds"), ["tlsf_align((s : \{w}))"]),
        ),
        arw([]),
        strip,
        have("16 <= val(\{r})", @int.asm_arith_tac),
        @tactics.mp_tac(inst(thm("tlsf_class"), [r])),
        arw([]),
        strip,
        @tactics.mp_tac(inst(thm("tlsf_class"), ["tlsf_size((hd : \{w}))"])),
        arw([]),
        strip,
        have(
          "val(tlsf_align((s : \{w}))) <= val(tlsf_size((hd : \{w})))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_find_sound"), [
                "tlsf_align((s : \{w}))",
                "tlsf_size((hd : \{w}))",
              ]),
            ),
            @tactics.rule_assum_tac(
              @simp.rewrite_rule(
                ths([
                  thm("tlsf_search_f"),
                  thm("tlsf_search_j"),
                  thm("tlsf_level_of"),
                  thm("tlsf_slot_of"),
                ]),
              ),
            ),
            @tactics.rule_assum_tac(
              @simp.rewrite_rule(
                ths([
                  @bool.undisch(inst(idx, [r])),
                  @bool.undisch(inst(idx, ["tlsf_size((hd : \{w}))"])),
                  thm("tlsf_code_sli"),
                ]),
              ),
            ),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        @int.asm_arith_tac,
      ])
    },
  )
  let head_member = lemma(
    "tlsf_head_member",
    "∀ xs : \{lw}, !(tlsf_hd(xs) == word(0)) → MEM(tlsf_hd(xs), xs)",
    () => {
      seq([
        @tactics.gen_tac,
        @tactics.struct_cases_tac(
          @bool.ispec(tm("(xs : \{lw})"), @lists.list_cases()),
        ),
        rw([thm("tlsf_hd"), @lists.mem()]),
      ])
    },
  )
  let bin_fit = lemma(
    "tlsf_bin_fit",
    "∀ s : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ f : Num, ∀ j : Num, ∀ m : \{w}, tlsf_layout(p, a, lim, top, xs, hd) && tlsf_bins_match(xs, hd, bl) && 16 <= val(s) && val(s) <= 4160749568 && f < 28 && j < 16 && m == tlsf_hd(bl(f)(j)) && !(m == word(0)) && (val(tlsf_search_f(s)) < f || (f == val(tlsf_search_f(s)) && val(tlsf_search_j(s)) <= j)) → MEM(m, xs) && !tlsf_used(hd(m)) && val(s) <= val(tlsf_size(hd(m)))",
    () => {
      seq([
        gen,
        strip,
        have(
          "MEM((m : \{w}), (bl : \{bt})((f : Num))((j : Num)))",
          @meson.asm_meson_tac(ths([head_member])),
        ),
        have(
          "MEM((m : \{w}), (xs : \{lw})) && !tlsf_used((hd : \{ht})(m)) && tlsf_level_of(hd(m)) == (f : Num) && tlsf_slot_of(hd(m)) == (j : Num)",
          @meson.asm_meson_tac(
            ths([
              inst(thm("tlsf_bins_match_member"), [
                "(xs : \{lw})",
                "(hd : \{ht})",
                "(bl : \{bt})",
                "(m : \{w})",
                "(f : Num)",
                "(j : Num)",
              ]),
            ]),
          ),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        have(
          "tlsf_block_ok(val((m : \{w})), (lim : Num), m, (hd : \{ht}))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_layout_members"), [
                "(xs : \{lw})",
                "(p : \{w})",
                "(a : Num)",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(m : \{w})",
              ]),
            ),
            arw([]),
          ]),
        ),
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_block_ok")]))),
        @meson.asm_meson_tac(
          ths([inst(size_sound, ["(s : \{w})", "(hd : \{ht})((m : \{w}))"])]),
        ),
      ])
    },
  )
  let prep_bounds = lemma(
    "tlsf_search_class_bounds",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= 4160749568 → val(tlsf_search_f(s)) < 28 && val(tlsf_search_j(s)) < 16",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(align_bounds, ["(s : \{w})"])),
        arw([]),
        strip,
        have("16 <= val(tlsf_align((s : \{w})))", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("tlsf_round_bounds"), ["tlsf_align((s : \{w}))"]),
        ),
        arw([]),
        strip,
        have("16 <= val(\{r})", @int.asm_arith_tac),
        @tactics.mp_tac(inst(thm("tlsf_code_bounds"), [r])),
        arw([thm("tlsf_search_f"), thm("tlsf_search_j")]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let ct = (x : String) => "(word(word_ctz(\{x})) : \{w})"
  let va = (x : String) => "val((\{x} : \{w}))"
  let ff = ct("word_and((fl : \{w}), tlsf_cut(tlsf_search_f((s : \{w}))))")
  let jj = ct(
    "word_and((sb : (Num) -> \{w})(\{va(ff)}), tlsf_cut(tlsf_search_j((s : \{w}))))",
  )
  let gg = ct(
    "word_and((fl : \{w}), word_jshl(tlsf_cut(tlsf_search_f((s : \{w}))), word(1)))",
  )
  let kk = ct("(sb : (Num) -> \{w})(\{va(gg)})")
  let neq = (x : String) => "!(\{x} == word(32))"
  let np = "(f : Num) => !((sb : (Num) -> \{w})(f) == word(0))"
  let pre = "tlsf_tables_sync((fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})) && 16 <= val((s : \{w})) && val(s) <= 4160749568"
  let common = "∀ s : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}"
  let prep = seq([
    @tactics.mp_tac(inst(prep_bounds, ["(s : \{w})"])),
    arw([]),
    strip,
    have(
      "val(tlsf_search_f((s : \{w}))) < 32 && val(tlsf_search_j(s)) < 32",
      @int.asm_arith_tac,
    ),
  ])
  let row_sync = (fw : String) => {
    have(
      "tlsf_sync((sb : (Num) -> \{w})(\{va(fw)}), 16, (j : Num) => !((bl : \{bt})(\{va(fw)})(j) == NIL))",
      seq([
        @tactics.first_x_assum(th => {
          @tactics.match_mp_tac(@bool.spec(tm(va(fw)), th))
        }),
        arw([]),
      ]),
    )
  }
  let direct = lemma(
    "tlsf_search_direct_class",
    "\{common}, \{pre} && \{neq(ff)} && \{neq(jj)} → \{va(ff)} < 28 && \{va(jj)} < 16 && (val(tlsf_search_f(s)) < \{va(ff)} || (\{va(ff)} == val(tlsf_search_f(s)) && val(tlsf_search_j(s)) <= \{va(jj)}))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_tables_sync")]),
        strip,
        prep,
        @tactics.mp_tac(
          inst(thm("tlsf_masked_index"), [
            "(fl : \{w})",
            "tlsf_search_f((s : \{w}))",
            "28",
            np,
          ]),
        ),
        arw([]),
        strip,
        row_sync(ff),
        @tactics.mp_tac(
          inst(thm("tlsf_masked_index"), [
            "(sb : (Num) -> \{w})(\{va(ff)})",
            "tlsf_search_j((s : \{w}))",
            "16",
            "(j : Num) => !((bl : \{bt})(\{va(ff)})(j) == NIL)",
          ]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let fallback = lemma(
    "tlsf_search_next_class",
    "\{common}, \{pre} && \{neq(gg)} && \{neq(kk)} → \{va(gg)} < 28 && \{va(kk)} < 16 && val(tlsf_search_f(s)) < \{va(gg)}",
    () => {
      seq([
        gen,
        rw([thm("tlsf_tables_sync")]),
        strip,
        prep,
        @tactics.mp_tac(
          inst(thm("tlsf_next_index"), [
            "(fl : \{w})",
            "tlsf_search_f((s : \{w}))",
            "28",
            np,
          ]),
        ),
        arw([]),
        strip,
        row_sync(gg),
        @tactics.mp_tac(
          inst(thm("tlsf_ctz_plain_range"), [
            "(sb : (Num) -> \{w})(\{va(gg)})",
            "16",
            "(j : Num) => !((bl : \{bt})(\{va(gg)})(j) == NIL)",
          ]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let search = "tlsf_search((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let good = (m : String) => {
    "(\{m} == word(0) || (MEM(\{m}, (xs : \{lw})) && !tlsf_used((hd : \{ht})(\{m})) && val((s : \{w})) <= val(tlsf_size(hd(\{m})))))"
  }
  let finish = (fw : String, jw : String, cls : @kernel.Thm) => {
    seq([
      @tactics.mp_tac(
        inst(cls, [
          "(s : \{w})",
          "(fl : \{w})",
          "(sb : (Num) -> \{w})",
          "(bl : \{bt})",
        ]),
      ),
      arw([]),
      strip,
      @class.asm_cases_tac(
        tm("tlsf_hd((bl : \{bt})(\{va(fw)})(\{va(jw)})) == word(0)"),
      ),
      arw([]),
      @tactics.mp_tac(
        inst(bin_fit, [
          "(s : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "(lim : Num)",
          "(top : \{w})",
          "(xs : \{lw})",
          "(hd : \{ht})",
          "(bl : \{bt})",
          va(fw),
          va(jw),
          "tlsf_hd((bl : \{bt})(\{va(fw)})(\{va(jw)}))",
        ]),
      ),
      @simp.asm_simp_tac(ths([])),
      @tactics.try_tac(@int.asm_arith_tac),
    ])
  }
  let _ = lemma(
    "tlsf_search_sound",
    "\{common}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, \{pre} && tlsf_layout(p, a, lim, top, xs, hd) && tlsf_bins_match(xs, hd, bl) → \{good(search)}",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_search")]),
        @class.asm_cases_tac(tm("\{ff} == word(32)")),
        arw([]),
        @tactics.thenl(
          @class.asm_cases_tac(tm("\{jj} == word(32)")),
          @list.List([
            seq([
              @class.asm_cases_tac(tm("\{gg} == word(32)")),
              arw([]),
              @class.asm_cases_tac(tm("\{kk} == word(32)")),
              arw([]),
              finish(gg, kk, fallback),
            ]),
            seq([arw([]), finish(ff, jj, direct)]),
          ]),
        ),
      ])
    },
  )
  def(
    "tlsf_find_result",
    "tlsf_find_result((s : \{w}), (xs : \{lw}), (hd : \{ht}), (m : \{w})) == (m == word(0) || (MEM(m, xs) && !tlsf_used(hd(m)) && val(s) <= val(tlsf_size(hd(m)))))",
  )
  let sync_frame = lemma(
    "tlsf_bins_sync_frame",
    "∀ d : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ p : \{hprop}, ∀ h : \{heap}, star(tlsf_bins(d, fl, sb, bl), p, h) → tlsf_tables_sync(fl, sb, bl)",
    () => {
      seq([
        gen,
        rw([thm("star")]),
        @meson.meson_tac(ths([thm("tlsf_bins_sync")])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_ro_domain",
    "∀ s : \{w}, ∀ d : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, tlsf_ro(d, fl, sb, bl, before, fp, gs, ms, h) → tlsf_search_domain(s, fl, sb)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_ro")]),
        @meson.meson_tac(ths([sync_frame, thm("tlsf_search_domain_sync")])),
      ])
    },
  )
  let large_tables = lemma(
    "tlsf_large_tables",
    "∀ d : \{w}, ∀ limit : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, tlsf_large(d, limit, top, xs, hd, fl, sb, bl, h) → tlsf_tables_sync(fl, sb, bl)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_large"), thm("star")]),
        @meson.meson_tac(ths([thm("tlsf_bins_sync")])),
      ])
    },
  )
  let large_sound = lemma(
    "tlsf_large_search_sound",
    "∀ s : \{w}, ∀ d : \{w}, ∀ limit : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, 16 <= val(s) && val(s) <= 4160749568 && tlsf_large(d, limit, top, xs, hd, fl, sb, bl, h) → tlsf_find_result(s, xs, hd, tlsf_search(s, fl, sb, bl))",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_find_result")]),
        @tactics.match_mp_tac(
          inst(thm("tlsf_search_sound"), [
            "(s : \{w})",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(word(0) : \{w})",
            "tlsf_origin((d : \{w}))",
            "(limit : Num)",
            "(top : \{w})",
            "(xs : \{lw})",
            "(hd : \{ht})",
          ]),
        ),
        @meson.asm_meson_tac(
          ths([large_tables, thm("tlsf_large_layout"), thm("tlsf_large")]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_large_search_sound_frame",
    "∀ s : \{w}, ∀ d : \{w}, ∀ limit : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ p : \{hprop}, ∀ h : \{heap}, 16 <= val(s) && val(s) <= 4160749568 && star(tlsf_large(d, limit, top, xs, hd, fl, sb, bl), p, h) → tlsf_find_result(s, xs, hd, tlsf_search(s, fl, sb, bl))",
    () => seq([gen, rw([thm("star")]), @meson.meson_tac(ths([large_sound]))]),
  )
}
