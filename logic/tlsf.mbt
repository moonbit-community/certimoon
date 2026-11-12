// TLSF's size classes, as MoonBit's allocator computes them
// (moonbitlang/malloc, src/memory.mbt): a size s, at least 16, is in the
// class (fli, sli), where fli = 31 - clz(s), the index of s's highest bit,
// and sli = (s >> (fli - 4)) & 15, the 4 bits below it. The class (f, j)
// holds the sizes from (16 + j) * 2^(f - 4) up to (17 + j) * 2^(f - 4).
// find(size) rounds the request up (round_up_for_search) and looks in the
// rounded size's class and the classes above it. The definitions are the
// operations of the compiled code: i32.clz, i32.shr_u and i32.shl, which
// take the count modulo 32 (word_jushr, word_jshl), wrapping i32.add and
// i32.sub.
//
// tlsf_find_sound: every size in the class find picks, or in a class
// above it, is at least the request. tlsf_class_mono: a larger size is
// never in a lower class, so find finds a free block when one is at least
// the rounded request. tlsf_round_bounds: up to MAX_REQUEST_SIZE
// (0xF8000000) rounding neither wraps nor adds a class's width, and the
// rounded size is the least of its class.

///|
/// `th`, with numerals computed.
fn red(th : @kernel.Thm) -> @kernel.Thm raise {
  @equal.conv_rule(@calc_num.num_reduce_conv, th)
}

///|
/// The facts as antecedents of the goal, then `tac`.
fn given(facts : Array[@kernel.Thm], tac : @tactics.Tactic) -> @tactics.Tactic {
  let tacs = facts.map(th => @tactics.mp_tac(th))
  tacs.push(tac)
  seq(tacs)
}

///|
/// `th` for the terms `xs`.
fn inst(th : @kernel.Thm, xs : Array[String]) -> @kernel.Thm raise {
  @bool.ispecl(@list.List(xs.map(tm)), th)
}

///|
fn prove_tlsf_classes() -> Unit raise {
  let w = w32
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let intro = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let reduce = @tactics.conv_tac(@calc_num.num_reduce_conv)
  let arith_t = @int.asm_arith_tac
  let mp = (th : @kernel.Thm) => @tactics.mp_tac(th)
  let fl = (x : String) => "val(tlsf_fli(\{x}))"
  let k = (x : String) => "EXP(2, \{fl(x)} - 4)"
  let sl = (x : String) => "val(tlsf_sli(\{x}, tlsf_fli(\{x})))"
  let s = "(s : \{w})"
  let t = "(t : \{w})"
  let x = "(x : \{w})"
  let y = "(y : \{w})"
  let r = "tlsf_round(\{s})"
  let max = "4160749568"
  def(
    "tlsf_fli",
    "tlsf_fli((s : \{w})) == word_sub(word(31), int_clz(s))",
  )
  def(
    "tlsf_sli",
    "tlsf_sli((s : \{w}), (f : \{w})) == word_and(word_jushr(s, word_sub(f, word(4))), word(15))",
  )
  def(
    "tlsf_mask",
    "tlsf_mask((s : \{w})) == word_sub(word_jshl(word(1), word_sub(tlsf_fli(s), word(4))), word(1))",
  )
  def(
    "tlsf_round",
    "tlsf_round((s : \{w})) == word_and(word_add(s, tlsf_mask(s)), word_not(tlsf_mask(s)))",
  )
  // powers of 2
  let exp_le = lemma(
    "tlsf_exp_le",
    "∀ m : Num, ∀ n : Num, (EXP(2, m) <= EXP(2, n)) == (m <= n)",
    seq([gen, rw([@arith.le_exp()]), reduce, rw([])]),
  )
  let exp_lt = lemma(
    "tlsf_exp_lt",
    "∀ m : Num, ∀ n : Num, (EXP(2, m) < EXP(2, n)) == (m < n)",
    seq([gen, rw([@arith.lt_exp()]), reduce, rw([])]),
  )
  let exp_nz = lemma(
    "tlsf_exp_nz",
    "∀ n : Num, !(EXP(2, n) == 0)",
    seq([gen, rw([@arith.exp_eq_0()]), reduce, rw([])]),
  )
  let exp_fli = lemma(
    "tlsf_exp_fli",
    "∀ f : Num, 4 <= f → EXP(2, f) == 16 * EXP(2, f - 4) && EXP(2, f + 1) == 32 * EXP(2, f - 4) && EXP(2, f + 2) == 64 * EXP(2, f - 4) && EXP(2, f + 1 - 4) == 2 * EXP(2, f - 4)",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      have(
        "∃ k : Num, (f : Num) == k + 4",
        seq([@tactics.exists_tac(tm("(f : Num) - 4")), arith_t]),
      ),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      rw([arith("(k : Num) + 4 - 4 == k"), arith("(k : Num) + 4 + 1 - 4 == k + 1")]),
      rw([@arith.exp_add()]),
      reduce,
      @int.arith_tac,
    ]),
  )
  // the first-level index
  let clz_lt = have(
    "word_clz(\{s}) < 32",
    seq([mp(inst(@words.word_clz_lt_dimindex(), [s])), rw([@words.dimindex_32()]), arw([])]),
  )
  let fli_clz = lemma(
    "tlsf_fli_clz",
    "∀ s : \{w}, !(s == word(0)) → val(tlsf_fli(s)) == 31 - word_clz(s)",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      clz_lt,
      have("word_clz(\{s}) <= 31", arith_t),
      have(
        "MOD(word_clz(\{s}), 4294967296) == word_clz(s)",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      rw([
        thm("tlsf_fli"),
        @wasm.thm("int_clz"),
        @words.val_word_sub_cases(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      reduce,
      arw([]),
    ]),
  )
  let fli_bounds = lemma(
    "tlsf_fli_bounds",
    "∀ s : \{w}, !(s == word(0)) → \{fl("s")} <= 31 && EXP(2, \{fl("s")}) <= val(s) && val(s) < EXP(2, \{fl("s")} + 1)",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      clz_lt,
      @simp.asm_simp_tac(ths([fli_clz])),
      have("31 - word_clz(\{s}) + 1 == 32 - word_clz(s)", arith_t),
      have("32 - (word_clz(\{s}) + 1) == 31 - word_clz(s)", arith_t),
      mp(inst(@words.word_le_clz_val(), [s, "word_clz(\{s})"])),
      mp(inst(@words.word_le_clz_val(), [s, "word_clz(\{s}) + 1"])),
      rw([@words.dimindex_32()]),
      arw([]),
      arith_t,
    ]),
  )
  let nonzero = (v : String) => have(
    "!(\{v} == word(0))",
    seq([rw([@equal.gsym(@words.val_eq_0())]), arith_t]),
  )
  let fli_val = lemma(
    "tlsf_fli_val",
    "∀ s : \{w}, ∀ f : Num, EXP(2, f) <= val(s) && val(s) < EXP(2, f + 1) → val(tlsf_fli(s)) == f",
    seq([
      gen,
      intro,
      have(
        "!(\{s} == word(0))",
        seq([
          rw([@equal.gsym(@words.val_eq_0())]),
          mp(inst(exp_nz, ["(f : Num)"])),
          arith_t,
        ]),
      ),
      mp(inst(fli_bounds, [s])),
      arw([]),
      intro,
      mp(inst(exp_lt, [fl(s), "(f : Num) + 1"])),
      mp(inst(exp_lt, ["(f : Num)", fl(s) + " + 1"])),
      arith_t,
    ]),
  )
  // the second-level index
  let sli_val = lemma(
    "tlsf_sli_val",
    "∀ s : \{w}, 16 <= val(s) → 4 <= \{fl("s")} && \{fl("s")} <= 31 && \{sl("s")} == MOD(DIV(val(s), \{k("s")}), 16)",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      nonzero(s),
      mp(inst(fli_bounds, [s])),
      arw([]),
      intro,
      have("4 <= \{fl(s)}", given([red(inst(exp_lt, ["4", fl(s) + " + 1"]))], arith_t)),
      have(
        "MOD(\{fl(s)} - 4, 32) == \{fl(s)} - 4",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      have("(word(15) : \{w}) == word(EXP(2, 4) - 1)", seq([reduce, rw([])])),
      rw([thm("tlsf_sli")]),
      arw([
        @words.val_word_and_mask_word(),
        @words.word_jushr(),
        @words.val_word_ushr(),
        @words.val_word_sub_cases(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      reduce,
      arw([]),
    ]),
  )
  let class_num = lemma(
    "tlsf_class_num",
    "∀ v : Num, ∀ k : Num, EXP(2, k + 4) <= v && v < EXP(2, k + 5) → 16 <= DIV(v, EXP(2, k)) && DIV(v, EXP(2, k)) < 32 && MOD(DIV(v, EXP(2, k)), 16) == DIV(v, EXP(2, k)) - 16 && DIV(v, EXP(2, k)) * EXP(2, k) <= v && v < DIV(v, EXP(2, k)) * EXP(2, k) + EXP(2, k)",
    seq([
      gen,
      rw([@arith.exp_add()]),
      reduce,
      mp(inst(exp_nz, ["(k : Num)"])),
      mp(inst(@arith.division(), ["(v : Num)", "EXP(2, (k : Num))"])),
      mp(inst(@arith.le_rdiv_eq(), ["EXP(2, (k : Num))", "(v : Num)", "16"])),
      mp(inst(@arith.rdiv_lt_eq(), ["EXP(2, (k : Num))", "(v : Num)", "32"])),
      mp(
        inst(@arith.mod_uniq(), [
          "DIV((v : Num), EXP(2, (k : Num)))", "16", "1", "DIV((v : Num), EXP(2, (k : Num))) - 16",
        ]),
      ),
      @tactics.spec_tac(tm("DIV((v : Num), EXP(2, (k : Num)))"), tm("(q : Num)")),
      @tactics.spec_tac(tm("MOD((v : Num), EXP(2, (k : Num)))"), tm("(r : Num)")),
      @tactics.spec_tac(tm("EXP(2, (k : Num))"), tm("(kk : Num)")),
      gen,
      @int.arith_tac,
    ]),
  )
  // the class's bounds, from the class_num of s with k = fli - 4
  let class_steps = (v : String) => {
    let q = "DIV(val(\{v}), \{k(v)})"
    [
      nonzero(v),
      mp(inst(fli_bounds, [v])),
      arw([]),
      intro,
      have("\{fl(v)} - 4 + 4 == \{fl(v)}", arith_t),
      have("\{fl(v)} - 4 + 5 == \{fl(v)} + 1", arith_t),
      mp(inst(class_num, ["val(\{v})", fl(v) + " - 4"])),
      arw([]),
      intro,
      have("16 + (\{q} - 16) == \{q}", arith_t),
      have("17 + (\{q} - 16) == \{q} + 1", arith_t),
    ]
  }
  let class_ = lemma(
    "tlsf_class",
    "∀ s : \{w}, 16 <= val(s) → 4 <= \{fl("s")} && \{fl("s")} <= 31 && \{sl("s")} < 16 && (16 + \{sl("s")}) * \{k("s")} <= val(s) && val(s) < (17 + \{sl("s")}) * \{k("s")}",
    seq(
      [@tactics.gen_tac, @tactics.disch_tac, mp(inst(sli_val, [s])), arw([]), intro] +
      class_steps(s) +
      [arw([]), rw([@arith.right_add_distrib(), @arith.mult_clauses()]), arw([]), arith_t],
    ),
  )
  // rounding up
  let mask_word = lemma(
    "tlsf_mask_word",
    "∀ s : \{w}, 16 <= val(s) → tlsf_mask(s) == word(\{k("s")} - 1)",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      mp(inst(class_, [s])),
      arw([]),
      intro,
      have(
        "MOD(\{fl(s)} - 4, 32) == \{fl(s)} - 4",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      have("\{k(s)} <= 134217728", given([red(inst(exp_le, [fl(s) + " - 4", "27"]))], arith_t)),
      have("1 <= \{k(s)}", given([inst(exp_nz, [fl(s) + " - 4"])], arith_t)),
      have(
        "MOD(\{k(s)}, 4294967296) == \{k(s)}",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      have(
        "MOD(\{k(s)} - 1, 4294967296) == \{k(s)} - 1",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      rw([thm("tlsf_mask"), @words.word_jshl(), @equal.gsym(@words.val_eq())]),
      rw([
        @words.val_word_sub_cases(),
        @words.val_word_shl(),
        @words.val_word(),
        @words.val_word_1(),
        @words.dimindex_32(),
        @arith.mult_clauses(),
      ]),
      reduce,
      arw([]),
    ]),
  )
  let m = "DIV(val(\{s}) + (\{k(s)} - 1), \{k(s)})"
  let round_val = lemma(
    "tlsf_round_val",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= \{max} → val(tlsf_round(s)) == \{k("s")} * DIV(val(s) + (\{k("s")} - 1), \{k("s")})",
    seq([
      @tactics.gen_tac,
      intro,
      mp(inst(class_, [s])),
      arw([]),
      intro,
      have("\{k(s)} <= 134217728", given([red(inst(exp_le, [fl(s) + " - 4", "27"]))], arith_t)),
      have("1 <= \{k(s)}", given([inst(exp_nz, [fl(s) + " - 4"])], arith_t)),
      have(
        "MOD(\{k(s)} - 1, 4294967296) == \{k(s)} - 1",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      have(
        "MOD(val(\{s}) + (\{k(s)} - 1), 4294967296) == val(s) + (\{k(s)} - 1)",
        seq([@tactics.match_mp_tac(@arith.mod_lt()), arith_t]),
      ),
      mp(inst(mask_word, [s])),
      arw([]),
      @tactics.disch_tac,
      rw([thm("tlsf_round")]),
      arw([
        @words.val_word_and_not_mask_word(),
        @words.val_word_add(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      reduce,
      arw([]),
    ]),
  )
  // a size that is a multiple of its class's width is the class's least
  let exact = lemma(
    "tlsf_class_exact",
    "∀ x : \{w}, 16 <= val(x) && MOD(val(x), \{k("x")}) == 0 → (16 + \{sl("x")}) * \{k("x")} == val(x)",
    seq(
      [@tactics.gen_tac, intro, mp(inst(sli_val, [x])), arw([]), intro] +
      class_steps(x) +
      [
        arw([]),
        given(
          [inst(@arith.division(), ["val(\{x})", k(x)]), inst(exp_nz, [fl(x) + " - 4"])],
          arith_t,
        ),
      ],
    ),
  )
  let kk = k(s)
  let f = fl(s)
  let case_small = seq([
    have(
      "val(tlsf_fli(\{r})) == \{f}",
      seq([
        @tactics.match_mp_tac(fli_val),
        arw([]),
        given([inst(@arith.lt_mult_rcancel(), [m, "32", kk]), inst(@arith.mult_sym(), [kk, m])], arith_t),
      ]),
    ),
    arw([@arith.mod_mult()]),
  ])
  let case_top = seq([
    have("\{m} == 32", arith_t),
    have("\{f} + 1 + 1 == \{f} + 2", arith_t),
    have(
      "val(tlsf_fli(\{r})) == \{f} + 1",
      seq([@tactics.match_mp_tac(fli_val), arw([]), given([inst(exp_nz, [f + " - 4"])], arith_t)]),
    ),
    have("\{kk} * 32 == (2 * \{kk}) * 16", arith_t),
    arw([@arith.mod_mult()]),
  ])
  let round_bounds = lemma(
    "tlsf_round_bounds",
    "∀ s : \{w}, 16 <= val(s) && val(s) <= \{max} → val(s) <= val(tlsf_round(s)) && val(tlsf_round(s)) < val(s) + \{k("s")} && (16 + \{sl("tlsf_round(s)")}) * \{k("tlsf_round(s)")} == val(tlsf_round(s))",
    seq([
      @tactics.gen_tac,
      intro,
      mp(inst(class_, [s])),
      arw([]),
      intro,
      nonzero(s),
      mp(inst(fli_bounds, [s])),
      arw([]),
      intro,
      mp(inst(exp_fli, [f])),
      arw([]),
      intro,
      mp(inst(round_val, [s])),
      arw([]),
      @tactics.disch_tac,
      have(
        "16 <= \{m} && \{m} <= 32 && val(\{s}) <= \{kk} * \{m} && \{kk} * \{m} < val(s) + \{kk}",
        given(
          [
            inst(@arith.division(), ["val(\{s}) + (\{kk} - 1)", kk]),
            inst(exp_nz, [f + " - 4"]),
            inst(@arith.le_mult_rcancel(), ["16", m, kk]),
            inst(@arith.lt_mult_rcancel(), [m, "33", kk]),
            inst(@arith.mult_sym(), [kk, m]),
          ],
          arith_t,
        ),
      ),
      have("16 <= \{kk} * \{m}", arith_t),
      have(
        "(16 + \{sl(r)}) * \{k(r)} == val(\{r})",
        seq([
          @tactics.match_mp_tac(exact),
          arw([]),
          @class.asm_cases_tac(tm("\{m} <= 31")),
          @tactics.first(@list.List([solve(case_small), solve(case_top)])),
        ]),
      ),
      arw([]),
    ]),
  )
  // the theorems
  let _ = lemma(
    "tlsf_find_sound",
    "∀ s : \{w}, ∀ t : \{w}, 16 <= val(s) && val(s) <= \{max} && 16 <= val(t) && (\{fl("tlsf_round(s)")} < \{fl("t")} || (\{fl("t")} == \{fl("tlsf_round(s)")} && \{sl("tlsf_round(s)")} <= \{sl("t")})) → val(s) <= val(t)",
    seq([
      gen,
      intro,
      mp(inst(round_bounds, [s])),
      arw([]),
      intro,
      have("16 <= val(\{r})", arith_t),
      mp(inst(class_, [r])),
      arw([]),
      intro,
      mp(inst(exp_fli, [fl(r)])),
      arw([]),
      intro,
      mp(inst(class_, [t])),
      mp(inst(exp_le, [fl(r) + " + 1 - 4", fl(t) + " - 4"])),
      mp(inst(@arith.le_mult_rcancel(), [sl(r), "15", k(r)])),
      mp(inst(@arith.le_mult_rcancel(), [sl(r), sl(t), k(t)])),
      mp(inst(exp_nz, [fl(r) + " - 4"])),
      arw([]),
      arith_t,
    ]),
  )
  let _ = lemma(
    "tlsf_class_mono",
    "∀ x : \{w}, ∀ y : \{w}, 16 <= val(x) && val(x) <= val(y) → \{fl("x")} < \{fl("y")} || (\{fl("y")} == \{fl("x")} && \{sl("x")} <= \{sl("y")})",
    seq([
      gen,
      intro,
      have("16 <= val(\{y})", arith_t),
      nonzero(x),
      nonzero(y),
      mp(inst(fli_bounds, [x])),
      arw([]),
      intro,
      mp(inst(sli_val, [x])),
      arw([]),
      intro,
      have(
        "\{fl(x)} <= \{fl(y)}",
        seq([
          mp(inst(fli_bounds, [y])),
          arw([]),
          given([inst(exp_le, [fl(y) + " + 1", fl(x)])], arith_t),
        ]),
      ),
      @class.asm_cases_tac(tm("\{fl(x)} < \{fl(y)}")),
      @tactics.first(
        @list.List([
          solve(seq([@tactics.disj1_tac, arw([])])),
          solve(
            seq([
              @tactics.disj2_tac,
              have("\{fl(y)} == \{fl(x)}", arith_t),
              mp(inst(fli_bounds, [y])),
              mp(inst(sli_val, [y])),
              arw([]),
              intro,
              intro,
              have("\{fl(x)} - 4 + 4 == \{fl(x)}", arith_t),
              have("\{fl(x)} - 4 + 5 == \{fl(x)} + 1", arith_t),
              mp(inst(class_num, ["val(\{x})", fl(x) + " - 4"])),
              mp(inst(class_num, ["val(\{y})", fl(x) + " - 4"])),
              arw([]),
              intro,
              intro,
              arw([]),
              given([inst(@arith.div_mono(), ["val(\{x})", "val(\{y})", k(x)])], arith_t),
            ]),
          ),
        ]),
      ),
    ]),
  )
}

///|
/// TLSF's free lists: push and pop as the compiler embeds them
/// (moonbitlang/malloc's Memory::push and Memory::pop in the compiler's
/// lib/xml/wasm_linear/tlsf-mbt.wat, after both its wasm-opt passes; the
/// call of DATA_SECTION_END is the constant d it is linked as).
/// tools/tlsf_wat_check.py compares the programs with that file. A free
/// memory m has its size word at m and its free-list links at m + 8 (the
/// previous free memory) and m + 12 (the next). Level f's bitmap and bins
/// follow the first-level bitmap at base(d) = (d + 15) & ~15: at base + 4
/// + 68 (fli - 4), its bitmap, then a word for each of its 16 bins.
/// Each triple is about one path through the code, from exactly the words
/// it reads and writes (cells pts(a, serialise_i32(x)), framed by fp), the
/// other paths ruled out by its hypotheses. The code computes fli - 4 as
/// 27 - clz(s) (tlsf_code_fli) and the bin as tlsf_sli (tlsf_code_sli).
fn prove_tlsf_push_pop() -> Unit raise {
  let code_fli = lemma(
    "tlsf_code_fli",
    "∀ x : \{w32}, word_sub(word(27), word(word_clz(x))) == word_sub(tlsf_fli(x), word(4))",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([thm("tlsf_fli"), @wasm.thm("int_clz")])),
      g => @tactics.accept_tac(@words.word_rule(g.1))(g),
    ]),
  )
  let _ = lemma(
    "tlsf_code_sli",
    "∀ x : \{w32}, word_and(word_jushr(x, word_sub(word(27), word(word_clz(x)))), word(15)) == tlsf_sli(x, tlsf_fli(x))",
    seq([@tactics.gen_tac, @simp.rewrite_tac(ths([thm("tlsf_sli"), @equal.gsym(code_fli)]))]),
  )
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let c = (n : String) => "EConstNum(ConstInt32(word(\{n})))"
  let bin = (op : String) => "Binop(T_i32, Binop_i(\{op}))"
  let ld = "Load(T_i32, NONE, 2, 0)"
  let sto = "Store(T_i32, NONE, 2, 0)"
  let base_code = "EConstNum(ConstInt32(d)), \{c("15")}, \{bin("Add")}, \{c("4294967280")}, \{bin("And")}"
  // the bin of the memory at local 0: its size, fli - 4 and sli
  let index_code = (sz : Int, f : Int, j : Int) => [
    "Local_get(0)", ld, c("4294967292"), bin("And"), "Local_tee(\{sz})", c("27"), "Local_get(\{sz})",
    "Unop(T_i32, Unop_i(Clz))", bin("Sub"), "Local_tee(\{f})", bin("Shr(U)"), c("15"), bin("And"), "Local_set(\{j})",
  ].join(", ")
  let list = (xs : Array[String]) => "[" + xs.join(", ") + "]"
  let push_code = list([
    index_code(2, 1, 2),
    base_code, ld, c("1"), "Local_get(1)", bin("Shl"), bin("Or"), "Local_set(3)",
    base_code, "Local_get(3)", sto,
    base_code, c("4"), bin("Add"), "Local_get(1)", c("68"), bin("Mul"), bin("Add"), "Local_tee(1)",
    "Local_get(1)", ld, c("1"), "Local_get(2)", bin("Shl"), bin("Or"), sto,
    "Local_get(0)", c("12"), bin("Add"), "Local_get(1)", c("4"), bin("Add"), "Local_get(2)", c("2"), bin("Shl"),
    bin("Add"), ld, "Local_tee(3)", sto,
    "Local_get(3)", "If(Tbv(NONE), [Local_get(3), \{c("8")}, \{bin("Add")}, Local_get(0), \{sto}], NIL)",
    "Local_get(1)", c("4"), bin("Add"), "Local_get(2)", c("2"), bin("Shl"), bin("Add"), "Local_get(0)", sto,
    "Local_get(0)", "If(Tbv(NONE), [Local_get(0), \{c("8")}, \{bin("Add")}, \{c("0")}, \{sto}], NIL)",
    c("0"),
  ])
  let res = "Tbv(SOME(T_num(T_i32)))"
  let pop_then = list([
    "Local_get(1)", ld, "Local_tee(1)", c("12"), bin("Add"), "Local_get(0)", c("12"), bin("Add"), ld, "Local_tee(0)", sto,
    "Local_get(0)", "If(Tbv(NONE), [Local_get(0), \{c("8")}, \{bin("Add")}, Local_get(1), \{sto}], NIL)",
    c("0"),
  ])
  // as the compiler embeds it: after its second wasm-opt pass, pop has no
  // result (the outer if's 0 is dropped), and its bin's test is i32.eqz
  let pop_inner = list([
    "Local_get(3)", "Local_get(3)", ld, c("1"), "Local_get(2)", bin("Shl"), bin("Xor"), "Local_tee(0)", sto,
    "Local_get(0)", "Testop(T_i32, Eqz)",
    "If(Tbv(NONE), [\{base_code}, \{ld}, \{c("1")}, Local_get(1), \{bin("Shl")}, \{bin("Xor")}, Local_set(0), \{base_code}, Local_get(0), \{sto}], NIL)",
  ])
  let pop_else = list([
    index_code(1, 1, 2),
    base_code, c("4"), bin("Add"), "Local_get(1)", c("68"), bin("Mul"), bin("Add"), "Local_tee(3)",
    c("4"), bin("Add"), "Local_get(2)", c("2"), bin("Shl"), bin("Add"),
    "Local_get(0)", c("12"), bin("Add"), ld, "Local_tee(4)", sto,
    "Local_get(4)", "If(Tbv(NONE), [Local_get(4), \{c("8")}, \{bin("Add")}, \{c("0")}, \{sto}], NIL)",
    "Local_get(0)", c("12"), bin("Add"), ld, "Testop(T_i32, Eqz)",
    "If(Tbv(NONE), \{pop_inner}, NIL)",
    c("0"),
  ])
  let pop_code = list([
    "Local_get(0)", c("8"), bin("Add"), "Local_tee(1)", ld,
    "If(\{res}, \{pop_then}, \{pop_else})",
    "Drop",
  ])
  let push = program("tlsf_push_code", push_code, params=["(d : \{w})"])
  let pop = program("tlsf_pop_code", pop_code, params=["(d : \{w})"])
  // what the code computes
  let sz = "word_and(hd, word(4294967292))"
  let f4 = "word_sub(word(27), word(word_clz(\{sz})))"
  let sli = "word_and(word_jushr(\{sz}, \{f4}), word(15))"
  let base = "word_and(word_add(d, word(15)), word(4294967280))"
  let sl = "word_add(word_add(\{base}, word(4)), word_mul(\{f4}, word(68)))"
  let slot = "word_add(word_add(\{sl}, word(4)), word_jshl(\{sli}, word(2)))"
  let bit = (j : String) => "word_jshl(word(1), \{j})"
  let cell = (a : String, x : String) => "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  let rstate = (cells : Array[String]) => {
    let mut acc = "fp(gs, ms)"
    for k = cells.length() - 1; k >= 1; k = k - 1 {
      acc = "star(\{cells[k]}, \{acc})"
    }
    "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => star(\{cells[0]}, \{acc}, h)"
  }
  let state = (v : String, l : String, cells : Array[String]) => "st(\{v}, \{l}, \{rstate(cells)})"
  let nil = "(NIL : List[Value])"
  let z = i("word(0)")
  let ws = (xs : Array[String]) => xs.map(x => "∀ \{x} : \{w}").join(", ")
  let fpv = "∀ fp : \{rty}"
  let rws = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let at = (a : String, k : String) => "word_add(\{a}, word(\{k}))"
  // push, when the bin has a first memory nx, and when it is empty
  let fl2 = "word_or(fl, \{bit(f4)})"
  let slb2 = "word_or(slb, \{bit(sli)})"
  let push_locals = "[\{i("m")}, \{i(sl)}, \{i(sli)}, \{i("nx")}]"
  let push_case = (name : String, cons : Bool) => {
    let link = if cons { [cell(at("nx", "8"), "npf")] } else { [] }
    let link2 = if cons { [cell(at("nx", "8"), "m")] } else { [] }
    let pre = [cell("m", "hd"), cell(at("m", "8"), "pf0"), cell(at("m", "12"), "nf0"), cell(base, "fl"), cell(sl, "slb"), cell(slot, "nx")] + link
    let mid = [cell("m", "hd"), cell(at("m", "8"), "pf0"), cell(at("m", "12"), "nx"), cell(base, fl2), cell(sl, slb2), cell(slot, "nx")] + link2
    let post = [cell("m", "hd"), cell(at("m", "8"), "word(0)"), cell(at("m", "12"), "nx"), cell(base, fl2), cell(sl, slb2), cell(slot, "m")] + link2
    let hyp = if cons { "!(nx == word(0))" } else { "nx == word(0)" }
    let _ = sym_prove(
      name,
      "\{ws(["d", "m", "hd", "pf0", "nf0", "fl", "slb", "nx", "npf"])}, \{fpv}, !(m == word(0)) && \{hyp} → sl_triple(\{state(nil, "[\{i("m")}, \{z}, \{z}, \{z}]", pre)}, \{push}, \{state("[\{z}]", push_locals, post)})",
      [],
      [],
      afters=[state(nil, push_locals, mid), state(nil, push_locals, post)],
      rws~,
      kind="example",
    )
  }
  push_case("tlsf_push_cons", true)
  push_case("tlsf_push_nil", false)
  // pop: with a previous free memory pf (then nf, if not 0, links back to
  // it), or as its bin's first (then its bin starts at nf; if nf is 0 the
  // bin's bit goes, and if that was the level's last bit, the level's)
  let pop_pre = state(nil, "[\{i("m")}, \{z}, \{z}, \{z}, \{z}]", [cell(at("m", "8"), "pf")])
  let pop_mid = (pf_case : Bool, cons : Bool) => {
    let start = "[\{i("m")}, \{z}, \{z}, \{z}, \{z}]"
    let _ = start
    if pf_case {
      let link = if cons { [cell(at("nf", "8"), "pf")] } else { [] }
      let cells = [cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(at("pf", "12"), "nf")] + link
      [state(nil, "[\{i("nf")}, \{i("pf")}, \{z}, \{z}, \{z}]", cells), pop_pre, pop_pre]
    } else {
      let link = if cons { [cell(at("nf", "8"), "word(0)")] } else { [] }
      let cells = [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "nf")] + link
      let cells = if cons { cells } else { cells + [cell(sl, "slb"), cell(base, "fl")] }
      let locals = "[\{i("m")}, \{i(f4)}, \{i(sli)}, \{i(sl)}, \{i("nf")}]"
      let slb3 = "word_xor(slb, \{bit(sli)})"
      let fl3 = "(if \{slb3} == word(0) { word_xor(fl, \{bit(f4)}) } else { fl })"
      let l0 = "(if \{slb3} == word(0) { word_xor(fl, \{bit(f4)}) } else { \{slb3} })"
      let inner = state(
        nil,
        "[\{i(l0)}, \{i(f4)}, \{i(sli)}, \{i(sl)}, \{i("nf")}]",
        [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "nf"), cell(sl, slb3), cell(base, fl3)],
      )
      [pop_pre, state(nil, locals, cells), if cons { state(nil, locals, cells) } else { inner }]
    }
  }
  let pop_case = (name : String, pf_case : Bool, cons : Bool) => {
    let hyps = (if pf_case { "!(pf == word(0))" } else { "pf == word(0)" }) + " && " +
      (if cons { "!(nf == word(0))" } else { "nf == word(0)" })
    let (pre, post, locals) = if pf_case {
      let link = if cons { [cell(at("nf", "8"), "nn")] } else { [] }
      let link2 = if cons { [cell(at("nf", "8"), "pf")] } else { [] }
      (
        [cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(at("pf", "12"), "pn")] + link,
        [cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(at("pf", "12"), "nf")] + link2,
        "[\{i("nf")}, \{i("pf")}, \{z}, \{z}, \{z}]",
      )
    } else if cons {
      (
        [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "sv"), cell(at("nf", "8"), "nn")],
        [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "nf"), cell(at("nf", "8"), "word(0)")],
        "[\{i("m")}, \{i(f4)}, \{i(sli)}, \{i(sl)}, \{i("nf")}]",
      )
    } else {
      let slb3 = "word_xor(slb, \{bit(sli)})"
      let fl3 = "(if \{slb3} == word(0) { word_xor(fl, \{bit(f4)}) } else { fl })"
      let l0 = "(if \{slb3} == word(0) { word_xor(fl, \{bit(f4)}) } else { \{slb3} })"
      (
        [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "sv"), cell(sl, "slb"), cell(base, "fl")],
        [cell("m", "hd"), cell(at("m", "8"), "pf"), cell(at("m", "12"), "nf"), cell(slot, "nf"), cell(sl, slb3), cell(base, fl3)],
        "[\{i(l0)}, \{i(f4)}, \{i(sli)}, \{i(sl)}, \{i("nf")}]",
      )
    }
    // the state, rewritten with the branch's equations as the goal is
    let same = seq([
      @tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }),
      @simp.asm_rewrite_tac(ths(rws)),
    ])
    let vcs = if pf_case || cons { [] } else { [same, same] }
    let _ = sym_prove(
      name,
      "\{ws(["d", "m", "hd", "pf", "nf", "pn", "nn", "sv", "fl", "slb"])}, \{fpv}, \{hyps} → sl_triple(\{state(nil, "[\{i("m")}, \{z}, \{z}, \{z}, \{z}]", pre)}, \{pop}, \{state(nil, locals, post)})",
      [],
      vcs,
      afters=[state("[\{z}]", locals, post)] + pop_mid(pf_case, cons),
      rws~,
      kind="example",
    )
  }
  pop_case("tlsf_pop_mid", true, true)
  pop_case("tlsf_pop_last", true, false)
  pop_case("tlsf_pop_head", false, true)
  pop_case("tlsf_pop_only", false, false)
}
