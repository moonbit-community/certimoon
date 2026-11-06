// example_array_sum: a loop that reads an array, with a comparison as its
// condition.
//
//   local.get 2; local.get 1; i32.lt_u                  ;; i < n
//   if
//     loop
//       local.get 3
//       local.get 0; local.get 2; i32.const 4; i32.mul; i32.add
//       i32.load                                        ;; the word at p + 4i
//       i32.add; local.set 3                            ;; acc += it
//       local.get 2; i32.const 1; i32.add; local.set 2  ;; i += 1
//       local.get 2; local.get 1; i32.lt_u; br_if 0     ;; again if i < n
//     end
//   end
//
// from locals [p, n, 0, 0] and the n words xs at p ends with locals
// [p, n, n, wsum(xs)] (the words' sum, as a word) and the array as it was,
// if p + 4n < 2^32. The invariant: locals [p, n, i, wsum(ys)] with the
// array xs = ys ++ [y] ++ zs and i = LENGTH(ys). The arithmetic and list
// facts sym_prove leaves are lemmas (asum_addr, asum_step, asum_exit,
// asum_entry, asum_none).

///|
fn prove_array_sum_lemmas() -> Unit raise {
  let w = w32
  let val_eq_0 = @equal.gsym(@words.val_eq_0())
  def("wsum", "wsum((NIL : List[\{w}])) == word(0) && wsum(CONS(x, xs)) == word_add(x, wsum(xs))")
  let wsum = thm("wsum")
  let _ = lemma(
    "wsum_snoc",
    "∀ ys : List[\{w}], ∀ y : \{w}, wsum(APPEND(ys, [y])) == word_add(wsum(ys), y)",
    seq([
      @lists.list_induct_tac,
      @simp.asm_rewrite_tac(ths([wsum, @lists.append(), @words.word_add_0(), @words.word_add_assoc()])),
    ]),
  )
  let val_lemmas = [@words.val_word_add(), @words.val_word_mul(), @words.val_word(), @words.dimindex_32()]
  let _ = lemma(
    "val_add_one",
    "∀ i : \{w}, ∀ n : \{w}, val(i) < val(n) → val(word_add(i, word(1))) == val(i) + 1",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.mp_tac(@bool.ispec(tm("(n : \{w})"), @words.val_bound())),
      @simp.rewrite_tac(ths(val_lemmas)),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @tactics.disch_tac,
      have("val((i : \{w})) + 1 < 4294967296", @int.asm_arith_tac),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
    ]),
  )
  let shape = "LENGTH((xs : List[\{w}])) == val((n : \{w})) && xs == APPEND((ys : List[\{w}]), CONS((y : \{w}), (zs : List[\{w}]))) && LENGTH(ys) == val((i : \{w}))"
  let vars = "∀ p : \{w}, ∀ n : \{w}, ∀ i : \{w}, ∀ xs : List[\{w}], ∀ ys : List[\{w}], ∀ y : \{w}, ∀ zs : List[\{w}]"
  // the facts the shape gives: i < n, written with the lengths
  let take_apart = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    subst_vars(),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_append(), @lists.length()]))),
  ])
  let _ = lemma(
    "asum_addr",
    "\{vars}, val(p) + 4 * val(n) < 4294967296 && \{shape} → val(word_add(p, word_mul(i, word(4)))) + 0 == val(p) + 4 * LENGTH(ys)",
    seq([
      take_apart,
      have("val((i : \{w})) * 4 < 4294967296", @int.asm_arith_tac),
      have("val((p : \{w})) + val((i : \{w})) * 4 < 4294967296", @int.asm_arith_tac),
      @simp.rewrite_tac(ths(val_lemmas)),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
  let i1 = "word_add((i : \{w}), word(1))"
  let _ = lemma(
    "asum_step",
    "\{vars}, \{shape} && word_ult(\{i1}, n) → (∃ y2 : \{w}, ∃ zs2 : List[\{w}], zs == CONS(y2, zs2) && LENGTH(APPEND(ys, [y])) == val(\{i1}))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.ispec(tm("(zs : List[\{w}])"), @lists.list_cases())),
      @simp.rewrite_tac(
        ths([@lists.cons_11(), @lists.not_cons_nil(), @equal.gsym(@lists.not_cons_nil()), @words.word_ult_v1()]),
      ),
      take_apart,
      have("val((i : \{w})) < val((n : \{w}))", @int.asm_arith_tac),
      have("val(\{i1}) == val((i : \{w})) + 1", @meson.asm_meson_tac(ths([thm("val_add_one")]))),
      @tactics.first(@list.List([
        // zs empty: i + 1 = n, which is not below n
        solve(@int.asm_arith_tac),
        seq([
          @tactics.exists_tac(tm("(h : \{w})")),
          @tactics.exists_tac(tm("(t : List[\{w}])")),
          @simp.asm_rewrite_tac(ths([@lists.length_append(), @lists.length()])),
          @int.asm_arith_tac,
        ]),
      ])),
    ]),
  )
  let _ = lemma(
    "asum_exit",
    "\{vars}, \{shape} && !word_ult(\{i1}, n) → \{i1} == n && word_add(wsum(ys), y) == wsum(xs)",
    seq([
      take_apart,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.word_ult_v1()]))),
      have("val((i : \{w})) < val((n : \{w}))", @int.asm_arith_tac),
      have("val(\{i1}) == val((i : \{w})) + 1", @meson.asm_meson_tac(ths([thm("val_add_one")]))),
      @tactics.conj_tac,
      @tactics.first(@list.List([
        solve(seq([@simp.rewrite_tac(ths([@equal.gsym(@words.val_eq())])), @int.asm_arith_tac])),
        solve(seq([
          have("(zs : List[\{w}]) == NIL", seq([@simp.rewrite_tac(ths([@equal.gsym(@lists.length_eq_nil())])), @int.asm_arith_tac])),
          subst_vars(),
          @simp.rewrite_tac(ths([thm("wsum_snoc")])),
        ])),
      ])),
    ]),
  )
  let _ = lemma(
    "asum_entry",
    "∀ n : \{w}, ∀ xs : List[\{w}], word_ult(word(0), n) && LENGTH(xs) == val(n) → (∃ y : \{w}, ∃ zs : List[\{w}], xs == CONS(y, zs))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.ispec(tm("(xs : List[\{w}])"), @lists.list_cases())),
      @simp.rewrite_tac(
        ths([@words.word_ult_v1(), @words.val_word_0(), @lists.length(), @lists.cons_11(), @equal.gsym(@lists.not_cons_nil())]),
      ),
      @tactics.try_tac(@int.arith_tac),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "asum_none",
    "∀ n : \{w}, ∀ xs : List[\{w}], !word_ult(word(0), n) && LENGTH(xs) == val(n) → n == word(0) && xs == NIL",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([@words.word_ult_v1(), @words.val_word_0(), val_eq_0, @equal.gsym(@lists.length_eq_nil())])),
      @int.arith_tac,
    ]),
  )
}

///|
fn prove_example_array_sum() -> Unit raise {
  prove_array_sum_lemmas()
  let w = w32
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let array = (l : String) => "(gs : List[Value]) => (ms : Num) => star(arr(val(p), \{l}), fp(gs, ms))"
  let lt = "Relop_i(Lt(U))"
  let body = "[Local_get(3), Local_get(0), Local_get(2), EConstNum(ConstInt32(word(4))), Binop(T_i32, Binop_i(Mul)), Binop(T_i32, Binop_i(Add)), Load(T_i32, NONE, 2, 0), Binop(T_i32, Binop_i(Add)), Local_set(3), Local_get(2), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Add)), Local_set(2), Local_get(2), Local_get(1), Relop(T_i32, \{lt}), Br_if(0)]"
  let code = "[Local_get(2), Local_get(1), Relop(T_i32, \{lt}), If(Tbv(NONE), [Loop(Tbv(NONE), \{body})], NIL)]"
  let inv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ i : \{w}, ∃ ys : List[\{w}], ∃ y : \{w}, ∃ zs : List[\{w}], lc == [\{i_("(p : \{w})")}, \{i_("(n : \{w})")}, \{i_("i")}, \{i_("wsum(ys)")}] && (xs : List[\{w}]) == APPEND(ys, CONS(y, zs)) && LENGTH(ys) == val(i) && star(arr(val(p), APPEND(ys, CONS(y, zs))), (fp : \{rty})(gs, ms), h)"
  let args = ["p", "n", "i", "xs", "ys", "y", "zs"].map(v => "(\{v} : \{if v.has_suffix("s") { "List[\{w}]" } else { w }})")
  let _ = sym_prove(
    "example_array_sum",
    "∀ vs0 : List[Value], ∀ n : \{w}, ∀ p : \{w}, ∀ xs : List[\{w}], ∀ fp : \{rty}, LENGTH(xs) == val(n) && val(p) + 4 * val(n) < 4294967296 → sl_triple(st(vs0, [\{i_("p")}, \{i_("n")}, \{i_("word(0)")}, \{i_("word(0)")}], \{array("xs")}), \{code}, st(vs0, [\{i_("p")}, \{i_("n")}, \{i_("n")}, \{i_("wsum(xs)")}], \{array("xs")}))",
    [inv],
    [
      // entry: xs is y :: zs, none read yet
      seq([
        by_lemma(thm("asum_entry"), ["(n : \{w})", "(xs : List[\{w}])"]),
        subst_vars(),
        @tactics.exists_tac(tm("(NIL : List[\{w}])")),
        @tactics.exists_tac(tm("(y : \{w})")),
        @tactics.exists_tac(tm("(zs : List[\{w}])")),
        @simp.asm_rewrite_tac(ths([thm("wsum"), @lists.append(), @lists.length(), @words.val_word_0()])),
      ]),
      // the word read is at p + 4i
      by_lemma(thm("asum_addr"), args),
      // the invariant again, with y read
      seq([
        by_lemma(thm("asum_step"), args),
        subst_vars(),
        @tactics.exists_tac(tm("APPEND((ys : List[\{w}]), [(y : \{w})])")),
        @tactics.exists_tac(tm("(y2 : \{w})")),
        @tactics.exists_tac(tm("(zs2 : List[\{w}])")),
        @simp.asm_rewrite_tac(ths([thm("wsum_snoc"), @equal.gsym(@lists.append_assoc()), @lists.append()])),
      ]),
      // out of the loop
      by_lemma(thm("asum_exit"), args),
      // n = 0: xs is empty
      seq([by_lemma(thm("asum_none"), ["(n : \{w})", "(xs : List[\{w}])"]), @simp.asm_rewrite_tac(ths([thm("wsum")]))]),
    ],
  )
}
