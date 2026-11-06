// example_fill: a loop that writes x into m words of memory from p0.
//
//   local.get 1
//   if
//     loop
//       local.get 0; i32.const x; i32.store            ;; word at p := x
//       local.get 0; i32.const 4; i32.add; local.set 0 ;; p += 4
//       local.get 1; i32.const 1; i32.sub; local.set 1 ;; c -= 1
//       local.get 1; br_if 0                           ;; again if c ≠ 0
//     end
//   end
//
// from locals [p0, m] and the array ys (m words) at p0 ends with locals
// [p0 + 4m, 0] and the array REPLICATE(m, x), if p0 + 4m < 2^32. The
// loop's invariant: locals [p, c], c ≠ 0, p = p0 + 4(m - c), and the array
// is (m - c) copies of x, then y :: zs (c words still to write).
// sym_prove runs the code; the arithmetic and list facts it leaves are
// lemmas (fill_entry, fill_step, fill_exit).

///|
fn prove_fill_lemmas() -> Unit raise {
  let w = w32
  let val_eq_0 = @equal.gsym(@words.val_eq_0())
  let _ = lemma(
    "val_sub_one",
    "∀ c : \{w}, !(c == word(0)) → val(word_sub(c, word(1))) == val(c) - 1",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([val_eq_0, @words.val_word_sub_cases(), @words.val_word_1()])),
      @tactics.disch_tac,
      have("1 <= val((c : \{w}))", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "val_add_four",
    "∀ p : \{w}, val(p) + 4 < 4294967296 → val(word_add(p, word(4))) == val(p) + 4",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([@words.val_word_add(), @words.val_word(), @words.dimindex_32()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
    ]),
  )
  let _ = lemma(
    "replicate_shift",
    "∀ k : Num, ∀ x : A, ∀ l : List[A], APPEND(REPLICATE(k, x), CONS(x, l)) == APPEND(REPLICATE(SUC(k), x), l)",
    seq([
      @nums.induct_tac,
      @simp.asm_rewrite_tac(ths([@lists.replicate(), @lists.append()])),
    ]),
  )
  let _ = lemma(
    "word_add_val",
    "∀ a : \{w}, ∀ b : \{w}, ∀ k : Num, val(a) + 4 == val(b) + k → word_add(a, word(4)) == word_add(b, word(k))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.subst1_tac(@equal.gsym(@bool.ispec(tm("(a : \{w})"), @words.word_val()))),
      @tactics.subst1_tac(@equal.gsym(@bool.ispec(tm("(b : \{w})"), @words.word_val()))),
      @simp.rewrite_tac(ths([@equal.gsym(@words.word_add_v1())])),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "fill_entry",
    "∀ m : \{w}, ∀ ys : List[\{w}], !(m == word(0)) && LENGTH(ys) == val(m) → (∃ y : \{w}, ∃ zs : List[\{w}], ys == CONS(y, zs) && SUC(LENGTH(zs)) == val(m))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.ispec(tm("(ys : List[\{w}])"), @lists.list_cases())),
      @simp.rewrite_tac(ths([val_eq_0, @lists.length(), @lists.cons_11()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let c1 = "word_sub((c : \{w}), word(1))"
  let inv = "val((p : \{w})) == val((p0 : \{w})) + 4 * (val((m : \{w})) - val(c)) && val(c) <= val(m) && SUC(LENGTH((zs : List[\{w}]))) == val(c)"
  let _ = lemma(
    "fill_step",
    "∀ p0 : \{w}, ∀ m : \{w}, ∀ p : \{w}, ∀ c : \{w}, ∀ x : \{w}, ∀ zs : List[\{w}], val(p0) + 4 * val(m) < 4294967296 && !(c == word(0)) && !(\{c1} == word(0)) && \{inv} → (∃ y2 : \{w}, ∃ zs2 : List[\{w}], zs == CONS(y2, zs2) && val(word_add(p, word(4))) == val(p0) + 4 * (val(m) - val(\{c1})) && val(\{c1}) <= val(m) && SUC(LENGTH(zs2)) == val(\{c1}) && APPEND(REPLICATE(val(m) - val(\{c1}), x), CONS(y2, zs2)) == APPEND(REPLICATE(val(m) - val(c), x), CONS(x, zs)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.ispec(tm("(zs : List[\{w}])"), @lists.list_cases())),
      @simp.rewrite_tac(ths([@lists.length(), @lists.cons_11(), @lists.not_cons_nil()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "val(\{c1}) == val((c : \{w})) - 1",
        @meson.asm_meson_tac(ths([thm("val_sub_one")])),
      ),
      have("!(val(\{c1}) == 0)", @meson.asm_meson_tac(ths([val_eq_0]))),
      @tactics.first(@list.List([
        // zs empty: c is 1, so c - 1 is 0
        solve(@int.asm_arith_tac),
        // zs = h :: t: the word just written joins the copies of x
        seq([
          have(
            "val(word_add((p : \{w}), word(4))) == val(p) + 4",
            seq([
              @tactics.match_mp_tac(thm("val_add_four")),
              @int.asm_arith_tac,
            ]),
          ),
          have(
            "val((m : \{w})) - (val((c : \{w})) - 1) == SUC(val(m) - val(c))",
            @int.asm_arith_tac,
          ),
          @tactics.exists_tac(tm("(h : \{w})")),
          @tactics.exists_tac(tm("(t : List[\{w}])")),
          @simp.asm_rewrite_tac(ths([thm("replicate_shift")])),
          @int.asm_arith_tac,
        ]),
      ])),
    ]),
  )
  let _ = lemma(
    "fill_exit",
    "∀ p0 : \{w}, ∀ m : \{w}, ∀ p : \{w}, ∀ c : \{w}, ∀ x : \{w}, ∀ zs : List[\{w}], \{c1} == word(0) && \{inv} → word_add(p, word(4)) == word_add(p0, word(4 * val(m))) && REPLICATE(val(m), x) == APPEND(REPLICATE(val(m) - val(c), x), CONS(x, zs))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([@words.word_sub_eq_0()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([@words.val_word_1(), arith("∀ n : Num, (SUC(n) == 1) == (n == 0)"), @lists.length_eq_nil()]),
        ),
      ),
      subst_vars(),
      // strip_tac split the conclusion: the pointer, then the array
      @tactics.try_tac(solve(seq([@tactics.match_mp_tac(thm("word_add_val")), @int.asm_arith_tac]))),
      @tactics.try_tac(
        seq([
          have("SUC(val((m : \{w})) - 1) == val(m)", @int.asm_arith_tac),
          @simp.asm_rewrite_tac(ths([@words.val_word_1(), thm("replicate_shift"), @lists.append_nil()])),
        ]),
      ),
    ]),
  )
}

///|
fn prove_example_fill() -> Unit raise {
  prove_fill_lemmas()
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let array = (xs : String) => "(gs : List[Value]) => (ms : Num) => star(arr(val(p0), \{xs}), fp(gs, ms))"
  let body = "[Local_get(0), EConstNum(ConstInt32(x)), Store(T_i32, NONE, 2, 0), Local_get(0), EConstNum(ConstInt32(word(4))), Binop(T_i32, Binop_i(Add)), Local_set(0), Local_get(1), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Sub)), Local_set(1), Local_get(1), Br_if(0)]"
  let code = "[Local_get(1), If(Tbv(NONE), [Loop(Tbv(NONE), \{body})], NIL)]"
  let inv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ p : \{w}, ∃ c : \{w}, ∃ y : \{w}, ∃ zs : List[\{w}], lc == [\{i("p")}, \{i("c")}] && !(c == word(0)) && val(p) == val((p0 : \{w})) + 4 * (val((m : \{w})) - val(c)) && val(c) <= val(m) && SUC(LENGTH(zs)) == val(c) && star(arr(val(p0), APPEND(REPLICATE(val(m) - val(c), (x : \{w})), CONS(y, zs))), (fp : \{rty})(gs, ms), h)"
  let args = ["(p0 : \{w})", "(m : \{w})", "(p : \{w})", "(c : \{w})", "(x : \{w})", "(zs : List[\{w}])"]
  let _ = sym_prove(
    "example_fill",
    "∀ ys : List[\{w}], ∀ vs0 : List[Value], ∀ p0 : \{w}, ∀ m : \{w}, ∀ x : \{w}, ∀ fp : \{rty}, LENGTH(ys) == val(m) && val(p0) + 4 * val(m) < 4294967296 → sl_triple(st(vs0, [\{i("p0")}, \{i("m")}], \{array("ys")}), \{code}, st(vs0, [\{i("word_add(p0, word(4 * val(m)))")}, \{i("word(0)")}], \{array("REPLICATE(val(m), x)")}))",
    [inv],
    [
      // entry: ys is y :: zs, none written yet
      seq([
        by_lemma(thm("fill_entry"), ["(m : \{w})", "(ys : List[\{w}])"]),
        subst_vars(),
        @tactics.exists_tac(tm("(y : \{w})")),
        @tactics.exists_tac(tm("(zs : List[\{w}])")),
        @simp.asm_rewrite_tac(
          ths([arith("∀ n : Num, n - n == 0"), @arith.mult_clauses(), @arith.add_clauses(), @lists.replicate(), @lists.append(), @arith.le_refl()]),
        ),
      ]),
      // the word written is at p
      @simp.rewrite_tac(ths([@lists.length_replicate(), @arith.add_clauses()])),
      // the invariant again
      seq([
        by_lemma(thm("fill_step"), args),
        subst_vars(),
        @tactics.exists_tac(tm("(y2 : \{w})")),
        @tactics.exists_tac(tm("(zs2 : List[\{w}])")),
        @simp.asm_rewrite_tac(ths([])),
      ]),
      // out of the loop
      seq([by_lemma(thm("fill_exit"), args), @simp.asm_rewrite_tac(ths([]))]),
      // m = 0: ys is empty
      seq([
        subst_vars(),
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.val_word_0(), @lists.length_eq_nil()]))),
        subst_vars(),
        @simp.asm_rewrite_tac(ths([@words.val_word_0(), @arith.mult_clauses(), @words.word_add_0(), @lists.replicate()])),
      ]),
    ],
  )
}
