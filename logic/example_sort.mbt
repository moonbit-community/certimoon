// example_insertion_sort: insertion sort of an array of i32 words, by
// their unsigned value. Locals [p, n, i, j, x]:
//
//   i32.const 1; local.set 2                          ;; i = 1
//   local.get 2; local.get 1; i32.lt_u                ;; i < n
//   if
//     loop
//       a[i]; local.set 4                             ;; x = a[i]
//       local.get 2; local.set 3                      ;; j = i
//       block
//         loop
//           local.get 3; i32.eqz; br_if 1             ;; j = 0: out
//           a[j - 1]; local.get 4; i32.le_u; br_if 1  ;; a[j - 1] <= x: out
//           &a[j]; a[j - 1]; i32.store                ;; a[j] = a[j - 1]
//           local.get 3; i32.const 1; i32.sub; local.set 3
//           br 0
//         end
//       end
//       &a[j]; local.get 4; i32.store                 ;; a[j] = x
//       local.get 2; i32.const 1; i32.add; local.set 2
//       local.get 2; local.get 1; i32.lt_u; br_if 0   ;; again if i < n
//     end
//   end
//
// where &a[k] is p + k * 4 and a[k] loads it. From n words xs at p (if
// p + 4n < 2^32), it leaves words ys there with sorted(ys) (PAIRWISE ≤ on
// their values) and perm(ys, xs) (each value as often).
//
// The outer loop keeps the array as ss ++ rs with ss (the first i words)
// sorted. The inner loop holds x aside: the array is L ++ [d] ++ G ++ rest,
// where L ++ G is ss, the words of G (already moved right) are above x, and
// d is a copy of a moved word (or x). Its abstract array, with x in the
// hole, L ++ [x] ++ G ++ rest, is a permutation of xs; moving a word right
// swaps it with x there. The isort_ lemmas are the facts about lists and
// words that the verification conditions need, one or two each.

///|
fn prove_sort_defs() -> Unit raise {
  let w = w32
  def("sorted", "sorted((xs : List[\{w}])) == PAIRWISE((a : \{w}) => (b : \{w}) => val(a) <= val(b), xs)")
  def(
    "perm",
    "perm((xs : List[\{w}]), (ys : List[\{w}])) == (∀ y : \{w}, LENGTH(FILTER((z : \{w}) => z == y, xs)) == LENGTH(FILTER((z : \{w}) => z == y, ys)))",
  )
}

///|
fn prove_example_sort() -> Unit raise {
  prove_sort_defs()
  prove_sort_lemmas()
  let w = w32
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let c = (x : String) => "EConstNum(ConstInt32(word(\{x})))"
  let add = "Binop(T_i32, Binop_i(Add))"
  let sub = "Binop(T_i32, Binop_i(Sub))"
  let mul = "Binop(T_i32, Binop_i(Mul))"
  // p + k * 4, for k computed by `k`
  let addr = (k : String) => "Local_get(0), \{k}, \{c("4")}, \{mul}, \{add}"
  let ai = addr("Local_get(2)")
  let aj = addr("Local_get(3)")
  let aj1 = addr("Local_get(3), \{c("1")}, \{sub}")
  let load = "Load(T_i32, NONE, 2, 0)"
  let store = "Store(T_i32, NONE, 2, 0)"
  let lt = "Relop(T_i32, Relop_i(Lt(U)))"
  let le = "Relop(T_i32, Relop_i(Le(U)))"
  let inner = "[Local_get(3), Testop(T_i32, Eqz), Br_if(1), \{aj1}, \{load}, Local_get(4), \{le}, Br_if(1), \{aj}, \{aj1}, \{load}, \{store}, Local_get(3), \{c("1")}, \{sub}, Local_set(3), Br(0)]"
  let outer = "[\{ai}, \{load}, Local_set(4), Local_get(2), Local_set(3), Block(Tbv(NONE), [Loop(Tbv(NONE), \{inner})]), \{aj}, Local_get(4), \{store}, Local_get(2), \{c("1")}, \{add}, Local_set(2), Local_get(2), Local_get(1), \{lt}, Br_if(0)]"
  let code = "[\{c("1")}, Local_set(2), Local_get(2), Local_get(1), \{lt}, If(Tbv(NONE), [Loop(Tbv(NONE), \{outer})], NIL)]"
  let p = "(p : \{w})"
  let n = "(n : \{w})"
  let xs = "(xs : List[\{w}])"
  let fp = "(fp : \{rty})"
  let mem = (l : String) => "star(arr(val(\{p}), \{l}), \{fp}(gs, ms), h)"
  let state = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) =>"
  let sassn = "(vs : List[Value]) => \{state}"
  let outer_inv = "\{state} ∃ i : \{w}, ∃ j0 : \{w}, ∃ x0 : \{w}, ∃ ss : List[\{w}], ∃ rs : List[\{w}], lc == [\{i_(p)}, \{i_(n)}, \{i_("i")}, \{i_("j0")}, \{i_("x0")}] && sorted(ss) && LENGTH(ss) == val(i) && val(i) < val(\{n}) && LENGTH(APPEND(ss, rs)) == val(\{n}) && perm(APPEND(ss, rs), \{xs}) && \{mem("APPEND(ss, rs)")}"
  let holding = "LENGTH(L) == val(j) && sorted(APPEND(L, G)) && ALL((g : \{w}) => val(x) < val(g), G) && LENGTH(APPEND(L, G)) == val((i : \{w})) && val(i) < val(\{n}) && LENGTH(APPEND(L, CONS(d, APPEND(G, rest)))) == val(\{n}) && perm(APPEND(L, CONS(x, APPEND(G, rest))), \{xs}) && \{mem("APPEND(L, CONS(d, APPEND(G, rest)))")}"
  let vars = "∃ j : \{w}, ∃ x : \{w}, ∃ L : List[\{w}], ∃ d : \{w}, ∃ G : List[\{w}], ∃ rest : List[\{w}]"
  let locals = "lc == [\{i_(p)}, \{i_(n)}, \{i_("(i : \{w})")}, \{i_("j")}, \{i_("x")}]"
  let inner_inv = "\{state} \{vars}, \{locals} && \{holding}"
  let after_inner = "\{sassn} \{vars}, vs == NIL && \{locals} && ALL((y : \{w}) => val(y) <= val(x), L) && \{holding}"
  let post = "\{sassn} ∃ ys : List[\{w}], ∃ i : \{w}, ∃ j : \{w}, ∃ x : \{w}, vs == vs0 && lc == [\{i_("p")}, \{i_("n")}, \{i_("i")}, \{i_("j")}, \{i_("x")}] && sorted(ys) && perm(ys, xs) && star(arr(val(p), ys), fp(gs, ms), h)"
  let _ = sym_prove(
    "example_insertion_sort",
    "∀ vs0 : List[Value], ∀ p : \{w}, ∀ n : \{w}, ∀ xs : List[\{w}], ∀ fp : \{rty}, LENGTH(xs) == val(n) && val(p) + 4 * val(n) < 4294967296 → sl_triple(st(vs0, [\{i_("p")}, \{i_("n")}, \{i_("word(0)")}, \{i_("word(0)")}, \{i_("word(0)")}], (gs : List[Value]) => (ms : Num) => star(arr(val(p), xs), fp(gs, ms))), \{code}, \{post})",
    [outer_inv, inner_inv],
    sort_vcs(),
    afters=[after_inner],
    rules=[
      "st_const", "st_binop", "st_testop", "st_relop", "st_local_get", "st_local_set",
      "st_arr_load_at", "st_arr_store_at",
    ],
  )
}

///|
/// What the sort's invariants need about sorted and perm.
fn prove_sort_lemmas() -> Unit raise {
  let w = w32
  let sorted_rws = [
    thm("sorted"),
    @lists.pairwise_append(),
    @lists.pairwise(),
    @equal.gsym(@lists.all_mem()),
    @lists.mem_append(),
    @lists.mem(),
  ]
  let _ = lemma("perm_refl", "∀ xs : List[\{w}], perm(xs, xs)", @simp.rewrite_tac(ths([thm("perm")])))
  let _ = lemma(
    "perm_swap",
    "∀ A : List[\{w}], ∀ e : \{w}, ∀ x : \{w}, ∀ ts : List[\{w}], ∀ ys : List[\{w}], perm(APPEND(A, CONS(e, CONS(x, ts))), ys) → perm(APPEND(A, CONS(x, CONS(e, ts))), ys)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("perm"), @lists.filter_append(), @lists.length_append(), @lists.filter()])),
      @tactics.disch_tac,
      @tactics.x_gen_tac(tm("(y : \{w})")),
      @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(y : \{w})"), th))),
      @class.asm_cases_tac(tm("(e : \{w}) == (y : \{w})")),
      @class.asm_cases_tac(tm("(x : \{w}) == (y : \{w})")),
      @simp.asm_rewrite_tac(ths([@lists.length()])),
    ]),
  )
  let le = arith("∀ a : Num, ∀ b : Num, a < b → a <= b")
  let _ = lemma(
    "sorted_insert",
    "∀ L : List[\{w}], ∀ x : \{w}, ∀ G : List[\{w}], sorted(APPEND(L, G)) && ALL((y : \{w}) => val(y) <= val(x), L) && ALL((g : \{w}) => val(x) < val(g), G) → sorted(APPEND(L, CONS(x, G)))",
    seq([@simp.rewrite_tac(ths(sorted_rws)), @meson.meson_tac(ths([le]))]),
  )
  let _ = lemma(
    "sorted_snoc_le",
    "∀ L : List[\{w}], ∀ e : \{w}, ∀ G : List[\{w}], ∀ x : \{w}, sorted(APPEND(L, CONS(e, G))) && val(e) <= val(x) → ALL((y : \{w}) => val(y) <= val(x), APPEND(L, [e]))",
    seq([
      @simp.rewrite_tac(ths(sorted_rws)),
      @meson.meson_tac(ths([arith("∀ a : Num, ∀ b : Num, ∀ c : Num, a <= b && b <= c → a <= c")])),
    ]),
  )
  let _ = lemma(
    "snoc_cases",
    "∀ l : List[A], l == NIL || (∃ l2 : List[A], ∃ e : A, l == APPEND(l2, [e]))",
    @meson.meson_tac(ths([@lists.append_butlast_last()])),
  )
  let _ = lemma(
    "list_update_snoc",
    "∀ l2 : List[A], ∀ e : A, ∀ d : A, ∀ r : List[A], ∀ x : A, list_update(APPEND(l2, CONS(e, CONS(d, r))), SUC(LENGTH(l2)), x) == APPEND(l2, CONS(e, CONS(x, r)))",
    seq([@lists.list_induct_tac, @simp.asm_rewrite_tac(ths([@wasm.thm("list_update"), @lists.append(), @lists.length()]))]),
  )
  prove_isort_lemmas()
}

///|
/// The verification conditions' facts, as lemmas.
fn prove_isort_lemmas() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let absurd = seq([have("F", @int.asm_arith_tac), @tactics.first_assum(th => @tactics.contr_tac(th))])
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let accept = @tactics.first_assum(th => @tactics.accept_tac(th))
  let vsub = (j : String, rhs : String) => have(
    "val(word_sub((\{j} : \{w}), word(1))) == \{rhs}",
    seq([
      @tactics.mp_tac(@bool.ispec(tm("(\{j} : \{w})"), thm("val_sub_one"))),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.disch_tac,
      @int.asm_arith_tac,
    ]),
  )
  let vadd = have(
    "val(word_add((i : \{w}), word(1))) == val(i) + 1",
    seq([@tactics.match_mp_tac(thm("val_add_one")), @tactics.exists_tac(tm("(n : \{w})")), accept]),
  )
  // the cases L = NIL and L = l2 ++ [e] (then substituted)
  let snoc = (nil : @tactics.Tactic, cons : @tactics.Tactic) => @tactics.thenl(
    @tactics.disj_cases_tac(@bool.ispec(tm("(L : \{lw})"), thm("snoc_cases"))),
    @list.List([
      seq([subst_vars(), nil]),
      seq([@tactics.first_x_assum(th => @tactics.strip_assume_tac(th)), subst_vars(), cons]),
    ]),
  )
  let assoc = [@equal.gsym(@lists.append_assoc()), @lists.append(), @lists.length_append(), @lists.length()]
  let le_x = "ALL((y : \{w}) => val(y) <= val(x), L)"
  let gt_x = (l : String) => "ALL((g : \{w}) => val(x) < val(g), \{l})"
  let m = "APPEND(L, CONS(d, APPEND(G, rest)))"
  let held = "APPEND(L, CONS(x, APPEND(G, rest)))"
  let vars = "∀ L : \{lw}, ∀ d : \{w}, ∀ G : \{lw}, ∀ rest : \{lw}, ∀ j : \{w}, ∀ x : \{w}, ∀ i : \{w}, ∀ n : \{w}, ∀ xs : \{lw}"
  let holding = "LENGTH(L) == val(j) && sorted(APPEND(L, G)) && \{gt_x("G")} && LENGTH(APPEND(L, G)) == val(i) && val(i) < val(n) && LENGTH(\{m}) == val(n) && perm(\{held}, xs)"
  let _ = lemma(
    "isort_bound",
    "∀ L : \{lw}, ∀ G : \{lw}, ∀ j : \{w}, ∀ i : \{w}, ∀ n : \{w}, LENGTH(L) == val(j) && LENGTH(APPEND(L, G)) == val(i) && val(i) < val(n) → val(j) < val(n) && (!(j == word(0)) → val(word_sub(j, word(1))) < val(n))",
    seq([
      gen,
      @simp.rewrite_tac(ths([@lists.length_append()])),
      strip,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([@int.asm_arith_tac, seq([@tactics.disch_tac, vsub("j", "val(j) - 1"), @int.asm_arith_tac])]),
      ),
    ]),
  )
  let _ = lemma(
    "isort_inner_entry",
    "∀ ss : \{lw}, ∀ rs : \{lw}, ∀ i : \{w}, ∀ n : \{w}, LENGTH(ss) == val(i) && val(i) < val(n) && LENGTH(APPEND(ss, rs)) == val(n) → (∃ r : \{w}, ∃ t : \{lw}, rs == CONS(r, t) && EL(val(i), APPEND(ss, CONS(r, t))) == r)",
    seq([
      gen,
      @tactics.struct_cases_tac(@bool.ispec(tm("(rs : \{lw})"), @lists.list_cases())),
      @simp.rewrite_tac(ths([@lists.length_append(), @lists.length(), @equal.gsym(@lists.not_cons_nil()), @lists.cons_11()])),
      strip,
      @tactics.first(@list.List([
        solve(absurd),
        seq([
          @tactics.exists_tac(tm("(h : \{w})")),
          @tactics.exists_tac(tm("(t : \{lw})")),
          @simp.rewrite_tac(ths([])),
          @tactics.undisch_then(
            tm("LENGTH((ss : \{lw})) == val((i : \{w}))"),
            th => @simp.rewrite_tac(ths([@equal.gsym(th), thm("el_split")])),
          ),
        ]),
      ])),
    ]),
  )
  let _ = lemma(
    "isort_empty",
    "∀ L : \{lw}, ∀ j : \{w}, ∀ x : \{w}, LENGTH(L) == val(j) && j == word(0) → \{le_x}",
    seq([
      gen,
      strip,
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.val_word_0(), @lists.length_eq_nil()]))),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.all()])),
    ]),
  )
  let word_ule = @words.word_ule_v1()
  let _ = lemma(
    "isort_stop",
    "∀ L : \{lw}, ∀ G : \{lw}, ∀ d : \{w}, ∀ M : \{lw}, ∀ x : \{w}, ∀ j : \{w}, LENGTH(L) == val(j) && !(j == word(0)) && sorted(APPEND(L, G)) && word_ule(EL(val(word_sub(j, word(1))), APPEND(L, CONS(d, M))), x) → \{le_x}",
    seq([
      gen,
      snoc(
        @simp.rewrite_tac(ths([@lists.all()])),
        seq([
          @simp.rewrite_tac(ths(assoc)),
          strip,
          vsub("j", "LENGTH((l2 : \{lw}))"),
          // the element read is e
          @tactics.first_x_assum(th => seq([
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th, thm("el_split"), word_ule]))),
            @tactics.assume_tac(th),
          ])),
          @tactics.match_mp_tac(thm("sorted_snoc_le")),
          @tactics.exists_tac(tm("(G : \{lw})")),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
    ]),
  )
  let l2 = "(l2 : \{lw})"
  let e = "(e : \{w})"
  let shifted = "APPEND(l2, CONS(e, APPEND(CONS(e, G), rest)))"
  let _ = lemma(
    "isort_shift",
    "\{vars}, !(j == word(0)) && !word_ule(EL(val(word_sub(j, word(1))), \{m}), x) && \{holding} → (∃ l2 : \{lw}, ∃ e : \{w}, LENGTH(l2) == val(word_sub(j, word(1))) && sorted(APPEND(l2, CONS(e, G))) && \{gt_x("CONS(e, G)")} && LENGTH(APPEND(l2, CONS(e, G))) == val(i) && LENGTH(\{shifted}) == val(n) && perm(APPEND(l2, CONS(x, APPEND(CONS(e, G), rest))), xs) && list_update(\{m}, val(j), EL(val(word_sub(j, word(1))), \{m})) == \{shifted})",
    seq([
      gen,
      snoc(
        seq([
          @simp.rewrite_tac(ths([@lists.length()])),
          strip,
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@equal.gsym(@words.val_eq_0())]))),
          absurd,
        ]),
        seq([
          @simp.rewrite_tac(ths(assoc + [@lists.all()])),
          strip,
          vsub("j", "LENGTH(\{l2})"),
          @tactics.first_x_assum(th => seq([
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th, thm("el_split"), word_ule]))),
            @tactics.assume_tac(th),
          ])),
          have("val((x : \{w})) < val(\{e})", @int.asm_arith_tac),
          have("val((j : \{w})) == SUC(LENGTH(\{l2}))", @int.asm_arith_tac),
          have(
            "perm(APPEND(\{l2}, CONS((x : \{w}), CONS(\{e}, APPEND((G : \{lw}), (rest : \{lw}))))), (xs : \{lw}))",
            seq([@tactics.match_mp_tac(thm("perm_swap")), accept]),
          ),
          @tactics.exists_tac(tm(l2)),
          @tactics.exists_tac(tm(e)),
          @simp.asm_rewrite_tac(ths([thm("el_split"), thm("list_update_snoc")])),
          @int.asm_arith_tac,
        ]),
      ),
    ]),
  )
  let inserted = "APPEND(L, CONS(x, G))"
  let _ = lemma(
    "isort_next",
    "\{vars}, \{le_x} && \{holding} && word_ult(word_add(i, word(1)), n) → sorted(\{inserted}) && LENGTH(\{inserted}) == val(word_add(i, word(1))) && val(word_add(i, word(1))) < val(n) && LENGTH(APPEND(\{inserted}, rest)) == val(n) && perm(APPEND(\{inserted}, rest), xs) && list_update(\{m}, val(j), x) == APPEND(\{inserted}, rest)",
    seq([
      gen,
      strip,
      vadd,
      have("sorted(APPEND((L : \{lw}), CONS((x : \{w}), (G : \{lw}))))", seq([@tactics.match_mp_tac(thm("sorted_insert")), @simp.asm_rewrite_tac(ths([]))])),
      @tactics.undisch_then(
        tm("LENGTH((L : \{lw})) == val((j : \{w}))"),
        th => @simp.rewrite_tac(ths([@equal.gsym(th), thm("list_update_split"), @equal.gsym(@lists.append_assoc()), @lists.append()])),
      ),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_append(), @lists.length(), @words.word_ult_v1()]))),
      @simp.asm_rewrite_tac(ths([@lists.length_append(), @lists.length()])),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "isort_done",
    "\{vars}, \{le_x} && \{holding} && !word_ult(word_add(i, word(1)), n) → sorted(list_update(\{m}, val(j), x)) && perm(list_update(\{m}, val(j), x), xs)",
    seq([
      gen,
      strip,
      vadd,
      have(
        "(rest : \{lw}) == NIL",
        seq([
          @simp.rewrite_tac(ths([@equal.gsym(@lists.length_eq_nil())])),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_append(), @lists.length(), @words.word_ult_v1()]))),
          @int.asm_arith_tac,
        ]),
      ),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.append_nil()]))),
      have("sorted(APPEND((L : \{lw}), CONS((x : \{w}), (G : \{lw}))))", seq([@tactics.match_mp_tac(thm("sorted_insert")), @simp.asm_rewrite_tac(ths([]))])),
      @tactics.undisch_then(
        tm("LENGTH((L : \{lw})) == val((j : \{w}))"),
        th => @simp.rewrite_tac(ths([@equal.gsym(th), thm("list_update_split"), @lists.append_nil()])),
      ),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "isort_start",
    "∀ xs : \{lw}, ∀ n : \{w}, LENGTH(xs) == val(n) && word_ult(word(1), n) → (∃ y : \{w}, ∃ zs : \{lw}, xs == CONS(y, zs) && sorted([y]) && LENGTH([y]) == val((word(1) : \{w})) && val((word(1) : \{w})) < val(n))",
    seq([
      gen,
      @tactics.struct_cases_tac(@bool.ispec(tm("(xs : \{lw})"), @lists.list_cases())),
      @simp.rewrite_tac(
        ths([@lists.length(), @words.word_ult_v1(), @words.val_word_1(), @lists.cons_11(), @equal.gsym(@lists.not_cons_nil()), thm("sorted"), @lists.pairwise(), @lists.all()]),
      ),
      strip,
      @tactics.first(@list.List([
        solve(absurd),
        seq([
          @tactics.exists_tac(tm("(h : \{w})")),
          @tactics.exists_tac(tm("(t : \{lw})")),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.try_tac(@int.asm_arith_tac),
        ]),
      ])),
    ]),
  )
  let _ = lemma(
    "isort_none",
    "∀ xs : \{lw}, ∀ n : \{w}, LENGTH(xs) == val(n) && !word_ult(word(1), n) → sorted(xs)",
    seq([
      gen,
      @tactics.struct_cases_tac(@bool.ispec(tm("(xs : \{lw})"), @lists.list_cases())),
      @tactics.try_tac(@tactics.struct_cases_tac(@bool.ispec(tm("(t : \{lw})"), @lists.list_cases()))),
      @simp.rewrite_tac(ths([thm("sorted"), @lists.pairwise(), @lists.all(), @lists.length(), @words.word_ult_v1(), @words.val_word_1()])),
      @tactics.try_tac(seq([strip, absurd])),
    ]),
  )
}


///|
/// The tactics for what sym_prove leaves of example_insertion_sort, in
/// order.
fn sort_vcs() -> Array[@tactics.Tactic] raise {
  let w = w32
  let lw = "List[\{w}]"
  let v = (x : String) => "(\{x} : \{w})"
  let l = (x : String) => "(\{x} : \{lw})"
  let exists = (ts : Array[String]) => seq(ts.map(t => @tactics.exists_tac(tm(t))))
  let close = @simp.asm_rewrite_tac(ths([]))
  // the same L, d, G and rest
  let same = exists([l("L"), v("d"), l("G"), l("rest")])
  let full = [l("L"), v("d"), l("G"), l("rest"), v("j"), v("x"), v("i"), v("n"), l("xs")]
  let bound = seq([by_lemma(thm("isort_bound"), [l("L"), l("G"), v("j"), v("i"), v("n")]), close])
  // rewrites the other assumptions (the memory) with the last one
  let memory = @tactics.first_x_assum(th => @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th]))))
  [
    // the outer loop's entry: the first word is sorted
    seq([
      by_lemma(thm("isort_start"), [l("xs"), v("n")]),
      subst_vars(),
      exists(["[(y : \{w})]", l("zs")]),
      @simp.asm_rewrite_tac(ths([@lists.append(), thm("perm_refl")])),
    ]),
    // the inner loop's entry: x is the next word, nothing moved yet
    seq([
      by_lemma(thm("isort_inner_entry"), [l("ss"), l("rs"), v("i"), v("n")]),
      subst_vars(),
      exists([l("ss"), v("r"), "(NIL : \{lw})", l("t")]),
      @simp.asm_rewrite_tac(ths([@lists.append_nil(), @lists.append(), @lists.all()])),
    ]),
    // j = 0: out, with nothing left of x
    seq([by_lemma(thm("isort_empty"), [l("L"), v("j"), v("x")]), same, close]),
    // a[j - 1] is inside the array
    bound,
    // a[j - 1] <= x: out
    seq([by_lemma(thm("isort_stop"), [l("L"), l("G"), v("d"), "APPEND(\{l("G")}, \{l("rest")})", v("x"), v("j")]), same, close]),
    bound,
    bound,
    // a[j] = a[j - 1]: the invariant again, one word further
    seq([by_lemma(thm("isort_shift"), full), memory, exists([l("l2"), v("e"), "CONS(\{v("e")}, \{l("G")})", l("rest")]), close]),
    bound,
    // a[j] = x: the outer loop's invariant again
    seq([by_lemma(thm("isort_next"), full), memory, exists(["APPEND(\{l("L")}, CONS(\{v("x")}, \{l("G")}))", l("rest")]), close]),
    // out of the outer loop: all sorted
    seq([by_lemma(thm("isort_done"), full), exists(["list_update(APPEND(\{l("L")}, CONS(\{v("d")}, APPEND(\{l("G")}, \{l("rest")}))), val(\{v("j")}), \{v("x")})"]), close]),
    // n <= 1: nothing to do
    seq([by_lemma(thm("isort_none"), [l("xs"), v("n")]), exists([l("xs")]), @simp.asm_rewrite_tac(ths([thm("perm_refl")]))]),
  ]
}
