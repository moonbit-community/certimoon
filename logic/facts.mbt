// Facts about lists and 32-bit words that hol_light's libraries do not
// have, shared by the rules and the examples: a list split as
// vi ++ [v] ++ vs with LENGTH(vi) = k, which is how EL(k, _) and
// list_update(_, k, _) are read (split_at, el_split, list_update_split,
// el_at, update_at); a list ending in x (snoc_eq, snoc_cases); and the
// value of a word plus or minus a small number (val_add_small,
// val_add_one, val_sub_one). The examples prove only the facts about their
// own programs.

///|
fn prove_list_facts() -> Unit raise {
  let list = [
    @lists.length(),
    @lists.append(),
    @lists.el(),
    @lists.hd(),
    @lists.tl(),
    @wasm.thm("list_update"),
    arith("∀ n : Num, !(n < 0)"),
    arith("∀ n : Num, 0 < SUC(n)"),
    arith("∀ m : Num, ∀ n : Num, (SUC(m) < SUC(n)) == (m < n)"),
    arith("∀ m : Num, ∀ n : Num, (SUC(m) == SUC(n)) == (m == n)"),
  ]
  // a list split at an index
  let _ = lemma(
    "split_at",
    "∀ l : List[A], ∀ k : Num, k < LENGTH(l) → (∃ vi : List[A], ∃ vs : List[A], LENGTH(vi) == k && l == APPEND(vi, CONS(EL(k, l), vs)))",
    seq([
      @lists.list_induct_tac,
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.spec(tm("(k : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths(list)),
      @tactics.first(@list.List([
        // the first element: vi is empty
        solve(seq([
          @tactics.exists_tac(tm("(NIL : List[A])")),
          @tactics.exists_tac(tm("(t : List[A])")),
          @simp.rewrite_tac(ths(list)),
        ])),
        // a later one: split the tail, and put the head on vi
        solve(seq([
          @tactics.disch_tac,
          @tactics.first_x_assum(ih => @tactics.first_assum(lt => @tactics.mp_tac(@drule.match_mp(ih)(lt)))),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.exists_tac(tm("CONS((h : A), (vi : List[A]))")),
          @tactics.exists_tac(tm("(vs : List[A])")),
          @simp.rewrite_tac(ths(list + [@lists.cons_11()])),
          @meson.asm_meson_tac(ths([])),
        ])),
      ])),
    ]),
  )
  let el_split = lemma(
    "el_split",
    "∀ vi : List[A], ∀ v : A, ∀ vs : List[A], EL(LENGTH(vi), APPEND(vi, CONS(v, vs))) == v",
    seq([@lists.list_induct_tac, @simp.asm_rewrite_tac(ths(list))]),
  )
  let update_split = lemma(
    "list_update_split",
    "∀ vi : List[A], ∀ v : A, ∀ vs : List[A], ∀ x : A, list_update(APPEND(vi, CONS(v, vs)), LENGTH(vi), x) == APPEND(vi, CONS(x, vs))",
    seq([@lists.list_induct_tac, @simp.asm_rewrite_tac(ths(list))]),
  )
  // the same, for a list written as such a split
  let _ = lemma(
    "el_at",
    "∀ l : List[A], ∀ vi : List[A], ∀ v : A, ∀ vs : List[A], ∀ k : Num, l == APPEND(vi, CONS(v, vs)) && LENGTH(vi) == k → EL(k, l) == v",
    seq([@tactics.repeat_tac(@tactics.strip_tac), subst_vars(), @tactics.match_accept_tac(el_split)]),
  )
  let _ = lemma(
    "update_at",
    "∀ l : List[A], ∀ vi : List[A], ∀ v : A, ∀ vs : List[A], ∀ k : Num, ∀ x : A, l == APPEND(vi, CONS(v, vs)) && LENGTH(vi) == k → list_update(l, k, x) == APPEND(vi, CONS(x, vs))",
    seq([@tactics.repeat_tac(@tactics.strip_tac), subst_vars(), @tactics.match_accept_tac(update_split)]),
  )
  let _ = lemma(
    "nonempty_cons",
    "∀ l0 : List[A], !(LENGTH(l0) == 0) → (∃ u : A, ∃ U2 : List[A], l0 == CONS(u, U2))",
    seq([
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.ispec(tm("(l0 : List[A])"), @lists.list_cases())),
      @simp.rewrite_tac(ths([@lists.length(), @lists.cons_11()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  // a list ending in x
  let _ = lemma(
    "snoc_eq",
    "∀ suf : List[A], ∀ x : A, ∀ l : List[A], APPEND(suf, [x]) == l == (!(l == NIL) && LAST(l) == x && suf == BUTLAST(l))",
    then_split(@tactics.repeat_tac(@tactics.gen_tac), @tactics.eq_tac, [
      seq([
        @tactics.disch_then(th => @tactics.subst1_tac(@equal.gsym(th))),
        @simp.rewrite_tac(
          ths([
            @lists.last_append(),
            @lists.butlast_append(),
            @lists.append_eq_nil(),
            @lists.not_cons_nil(),
            @lists.last(),
            @lists.butlast(),
            @lists.append_nil(),
          ]),
        ),
      ]),
      seq([
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        @tactics.match_mp_tac(@lists.append_butlast_last()),
        @simp.asm_rewrite_tac(ths([])),
      ]),
    ]),
  )
  let _ = lemma(
    "snoc_eq_sym",
    "∀ suf : List[A], ∀ x : A, ∀ l : List[A], l == APPEND(suf, [x]) == (!(l == NIL) && LAST(l) == x && suf == BUTLAST(l))",
    @meson.meson_tac(ths([thm("snoc_eq")])),
  )
  // to rewrite NIL == l before substituting: subst_var_tac would read it
  // as a definition of the constant NIL
  let _ = lemma(
    "nil_eq_sym",
    "∀ l : List[A], (NIL == l) == (l == NIL)",
    @meson.meson_tac(ths([])),
  )
  let _ = lemma(
    "snoc_cases",
    "∀ l : List[A], l == NIL || (∃ l2 : List[A], ∃ e : A, l == APPEND(l2, [e]))",
    @meson.meson_tac(ths([@lists.append_butlast_last()])),
  )
  // two splits of one list, with suffixes of the same length
  let _ = lemma(
    "append_len_eq",
    "∀ a : List[A], ∀ b : List[A], ∀ c : List[A], ∀ d : List[A], APPEND(a, b) == APPEND(c, d) && LENGTH(b) == LENGTH(d) → a == c && b == d",
    seq([
      @simp.rewrite_tac(ths([@wasm.thm("append_split")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([
            @lists.length_append(),
            arith("∀ x : Num, ∀ y : Num, (x == y + x) == (y == 0)"),
            arith("∀ x : Num, ∀ y : Num, (y + x == x) == (y == 0)"),
            @lists.length_eq_nil(),
          ]),
        ),
      ),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.append(), @lists.append_nil()])),
    ]),
  )
  let _ = lemma(
    "all_suffix",
    "∀ p : (A) -> Bool, ∀ a : List[A], ∀ b : List[A], ∀ c : List[A], ∀ d : List[A], APPEND(a, b) == APPEND(c, d) && ALL(p, APPEND(a, b)) → ALL(p, d)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.then_tac(
        @tactics.mp_tac(@bool.conjunct2(th)),
        @tactics.subst1_tac(@bool.conjunct1(th)),
      )),
      @simp.rewrite_tac(ths([@lists.all_append()])),
      @tactics.disch_then(th => @tactics.accept_tac(@bool.conjunct2(th))),
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
}

///|
fn prove_word_facts() -> Unit raise {
  let w = w32
  let val_add = [@words.val_word_add(), @words.val_word(), @words.dimindex_32()]
  let _ = lemma(
    "val_add_small",
    "∀ x : \{w}, ∀ k : Num, val(x) + k < 4294967296 → val(word_add(x, word(k))) == val(x) + k",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @simp.rewrite_tac(ths(val_add)),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      have("(k : Num) < 4294967296", @int.asm_arith_tac),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
    ]),
  )
  let _ = lemma(
    "val_add_one",
    "∀ i : \{w}, ∀ n : \{w}, val(i) < val(n) → val(word_add(i, word(1))) == val(i) + 1",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("val_add_small")),
      @tactics.mp_tac(@bool.ispec(tm("(n : \{w})"), @words.val_bound())),
      @simp.rewrite_tac(ths([@words.dimindex_32()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "val_sub_one",
    "∀ c : \{w}, !(c == word(0)) → val(word_sub(c, word(1))) == val(c) - 1",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([@equal.gsym(@words.val_eq_0()), @words.val_word_sub_cases(), @words.val_word_1()])),
      @tactics.disch_tac,
      have("1 <= val((c : \{w}))", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}
