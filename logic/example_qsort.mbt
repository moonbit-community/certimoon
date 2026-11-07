// example_quicksort: quicksort of an array of i32 words by their unsigned
// value, recursive, with Lomuto's partition as a function of its own.
//
// Function 0, quicksort(p, lo, hi), sorts the words lo..hi-1 of the array
// at p (a[k] is the word at p + 4k); local 3 is m:
//
//   if hi - lo < 2: return
//   m = partition(p, lo, hi)               ;; call 1
//   quicksort(p, lo, m)                    ;; call 0
//   quicksort(p, m + 1, hi)                ;; call 0
//
// Function 1, partition(p, lo, hi), with lo < hi; locals [p, lo, hi, i, j,
// pv, t]:
//
//   pv = a[hi - 1]; i = lo; j = lo
//   block
//     loop
//       j == hi - 1: br 1
//       if a[j] < pv:
//         t = a[i]; a[i] = a[j]; a[j] = t; i = i + 1
//       j = j + 1; br 0
//     end
//   end
//   t = a[i]; a[i] = pv; a[hi - 1] = t
//   i                                       ;; the result
//
// The specs (qsort_specs, qs_spec) are about the words A ++ B ++ Cs at p,
// with |A| = lo and |A ++ B| = hi: quicksort leaves A ++ ys ++ Cs, ys sorted
// and a permutation of B; partition (B = Bt ++ [pv]) leaves A ++ L ++ [pv]
// ++ G ++ Cs with the words of L below pv, those of G not, perm(L ++ G, Bt),
// and returns lo + |L|. The loop keeps the segment as L ++ G ++ Us ++ [pv],
// Us the words not looked at yet; a word below pv goes to the end of L, by
// a swap with the first word of G (which moves to G's end: rot).
//
// The partition's body has no calls: sym_prove proves it as an sl_triple
// (partition_body), and partition_fn makes it the body of function 1.
// Quicksort's body is run by sym_prove as a g triple, each call by its
// spec with the parts of the array chosen at the call (`calls`). sl_funs_g
// gives both specs (quicksort_specs), and example_quicksort is `call 0`
// on a whole array of n words.

///|
fn prove_example_qsort() -> Unit raise {
  prove_qsort_defs()
  prove_qsort_lemmas()
  prove_partition()
  prove_quicksort()
}

///|
fn prove_qsort_defs() -> Unit raise {
  let w = w32
  def("rot", "rot((NIL : List[\{w}])) == NIL && rot(CONS((g : \{w}), t)) == APPEND(t, [g])")
}

///|
/// Words, lists and permutations: what the partition's and quicksort's
/// verification conditions need.
fn prove_qsort_lemmas() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let rot = thm("rot")
  let assoc = @lists.append_assoc()
  let lists = [@lists.append(), @lists.append_nil(), @lists.length(), @lists.length_append()]
  let _ = lemma(
    "val_pred",
    "∀ x : \{w}, 0 < val(x) → val(word_sub(x, word(1))) == val(x) - 1",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([@words.val_word_sub_cases(), @words.val_word_1()])),
      @tactics.disch_tac,
      have("1 <= val((x : \{w}))", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "val_succ",
    "∀ x : \{w}, val(x) + 1 < 4294967296 → val(word_add(x, word(1))) == val(x) + 1",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([@words.val_word_add(), @words.val_word(), @words.dimindex_32()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
    ]),
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
  // EL and list_update at a place written as an APPEND
  let el_at = lemma(
    "el_at",
    "∀ l : List[A], ∀ vi : List[A], ∀ v : A, ∀ vs : List[A], ∀ k : Num, l == APPEND(vi, CONS(v, vs)) && LENGTH(vi) == k → EL(k, l) == v",
    seq([@tactics.repeat_tac(@tactics.strip_tac), subst_vars(), @tactics.match_accept_tac(thm("el_split"))]),
  )
  let upd_at = lemma(
    "update_at",
    "∀ l : List[A], ∀ vi : List[A], ∀ v : A, ∀ vs : List[A], ∀ k : Num, ∀ x : A, l == APPEND(vi, CONS(v, vs)) && LENGTH(vi) == k → list_update(l, k, x) == APPEND(vi, CONS(x, vs))",
    seq([@tactics.repeat_tac(@tactics.strip_tac), subst_vars(), @tactics.match_accept_tac(thm("list_update_split"))]),
  )
  // the same list, appended differently
  let same_list = seq([@simp.rewrite_tac(ths([@equal.gsym(assoc)] + lists)), @tactics.try_tac(@int.arith_tac)])
  let by_at = (th : @kernel.Thm, args : Array[String]) => seq([
    @tactics.match_mp_tac(@bool.ispecl(@list.List(args.map(tm)), th)),
    @tactics.conj_tac,
    same_list,
    seq([@simp.rewrite_tac(ths(lists)), @tactics.try_tac(@int.arith_tac)]),
  ])
  let x0 = "APPEND((A : \{lw}), APPEND((L : \{lw}), APPEND((G : \{lw}), CONS((u : \{w}), (R : \{lw})))))"
  let k1 = "LENGTH((A : \{lw})) + LENGTH((L : \{lw}))"
  let k2 = "\{k1} + LENGTH((G : \{lw}))"
  let _ = lemma(
    "el_mid",
    "∀ A : \{lw}, ∀ L : \{lw}, ∀ G : \{lw}, ∀ u : \{w}, ∀ R : \{lw}, EL(\{k2}, \{x0}) == u",
    seq([@tactics.repeat_tac(@tactics.gen_tac), by_at(el_at, [x0, "APPEND((A : \{lw}), APPEND((L : \{lw}), (G : \{lw})))", "(u : \{w})", "(R : \{lw})", k2])]),
  )
  let _ = lemma(
    "el_mid2",
    "∀ A : \{lw}, ∀ L : \{lw}, ∀ u : \{w}, ∀ R : \{lw}, EL(\{k1}, APPEND(A, APPEND(L, CONS(u, R)))) == u",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      by_at(el_at, ["APPEND((A : \{lw}), APPEND((L : \{lw}), CONS((u : \{w}), (R : \{lw}))))", "APPEND((A : \{lw}), (L : \{lw}))", "(u : \{w})", "(R : \{lw})", k1]),
    ]),
  )
  // the swap of the partition: the first word of G and u
  let g_cases = @tactics.struct_cases_tac(@bool.ispec(tm("(G : \{lw})"), @lists.list_cases()))
  let _ = lemma(
    "part_swap",
    "∀ A : \{lw}, ∀ L : \{lw}, ∀ G : \{lw}, ∀ u : \{w}, ∀ R : \{lw}, list_update(list_update(\{x0}, \{k1}, u), \{k2}, EL(\{k1}, \{x0})) == APPEND(A, APPEND(L, CONS(u, APPEND(rot(G), R))))",
    {
      let al = "APPEND((A : \{lw}), (L : \{lw}))"
      let u = "(u : \{w})"
      let r = "(R : \{lw})"
      let t = "(t : \{lw})"
      let h = "(h : \{w})"
      // rewrite the goal with the fact `stmt`, proved by `proof`
      let step = (stmt : String, proof : @tactics.Tactic) => seq([
        have(stmt, proof),
        @tactics.first_x_assum(th => @simp.rewrite_tac(ths([th]))),
      ])
      let nil_case = seq([
        step("EL(\{k1}, APPEND(A, APPEND(L, CONS(\{u}, \{r})))) == u", @tactics.match_accept_tac(thm("el_mid2"))),
        step(
          "list_update(APPEND(A, APPEND(L, CONS(\{u}, \{r}))), \{k1}, u) == APPEND(\{al}, CONS(u, R))",
          by_at(upd_at, ["APPEND(A, APPEND(L, CONS(\{u}, \{r})))", al, u, r, k1, u]),
        ),
        step(
          "list_update(APPEND(\{al}, CONS(\{u}, \{r})), \{k1}, u) == APPEND(\{al}, CONS(u, R))",
          by_at(upd_at, ["APPEND(\{al}, CONS(\{u}, \{r}))", al, u, r, k1, u]),
        ),
        same_list,
      ])
      let x1 = "APPEND(A, APPEND(L, CONS(\{h}, APPEND(\{t}, CONS(\{u}, \{r})))))"
      let y1 = "APPEND(\{al}, CONS(\{u}, APPEND(\{t}, CONS(\{u}, \{r}))))"
      let cons_case = seq([
        step("EL(\{k1}, \{x1}) == h", by_at(el_at, [x1, al, h, "APPEND(\{t}, CONS(\{u}, \{r}))", k1])),
        step("list_update(\{x1}, \{k1}, u) == \{y1}", by_at(upd_at, [x1, al, h, "APPEND(\{t}, CONS(\{u}, \{r}))", k1, u])),
        step(
          "list_update(\{y1}, \{k1} + SUC(LENGTH(\{t})), h) == APPEND(APPEND(\{al}, CONS(\{u}, \{t})), CONS(h, R))",
          by_at(upd_at, [y1, "APPEND(\{al}, CONS(\{u}, \{t}))", u, r, "\{k1} + SUC(LENGTH(\{t}))", h]),
        ),
        same_list,
      ])
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.thenl(
          seq([g_cases, @simp.rewrite_tac(ths([rot, @lists.append(), @lists.length(), arith("∀ n : Num, n + 0 == n")]))]),
          @list.List([nil_case, cons_case]),
        ),
      ])
    },
  )
  let filter_rws = [thm("perm"), @lists.filter_append(), @lists.length_append(), @lists.filter(), @lists.length()]
  let _ = lemma(
    "count_rot",
    "∀ P : (\{w}) -> Bool, ∀ G : \{lw}, LENGTH(FILTER(P, rot(G))) == LENGTH(FILTER(P, G))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      g_cases,
      @simp.rewrite_tac(ths([rot] + filter_rws)),
      @tactics.try_tac(seq([g => @class.cond_cases_tac(g), @simp.rewrite_tac(ths([@lists.length()])), @int.arith_tac])),
    ]),
  )
  let _ = lemma(
    "length_rot",
    "∀ G : \{lw}, LENGTH(rot(G)) == LENGTH(G)",
    seq([@tactics.gen_tac, g_cases, @simp.rewrite_tac(ths([rot] + lists)), @tactics.try_tac(@int.arith_tac)]),
  )
  let _ = lemma(
    "all_rot",
    "∀ P : (\{w}) -> Bool, ∀ G : \{lw}, ALL(P, rot(G)) == ALL(P, G)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      g_cases,
      @simp.rewrite_tac(ths([rot, @lists.all_append(), @lists.all()])),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  // perm by counting each value
  let by_counts = (cases : Array[String]) => seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths(filter_rws + [thm("count_rot")])),
    @tactics.disch_tac,
    @tactics.x_gen_tac(tm("(y : \{w})")),
    @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(y : \{w})"), th))),
    seq(cases.map(c => @class.asm_cases_tac(tm("(\{c} : \{w}) == (y : \{w})")))),
    @simp.asm_rewrite_tac(ths([@lists.length(), @lists.length_append(), thm("count_rot")])),
    @tactics.try_tac(@int.arith_tac),
  ])
  let _ = lemma(
    "perm_move",
    "∀ L : \{lw}, ∀ G : \{lw}, ∀ u : \{w}, ∀ R : \{lw}, ∀ Bt : \{lw}, perm(APPEND(L, APPEND(G, CONS(u, R))), Bt) → perm(APPEND(L, CONS(u, APPEND(rot(G), R))), Bt)",
    by_counts(["u"]),
  )
  let _ = lemma(
    "perm_rot",
    "∀ L : \{lw}, ∀ G : \{lw}, ∀ Bt : \{lw}, perm(APPEND(L, G), Bt) → perm(APPEND(L, rot(G)), Bt)",
    by_counts([]),
  )
}

///|
fn prove_partition() -> Unit raise {
  let w = w32
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let c = (x : String) => "EConstNum(ConstInt32(word(\{x})))"
  let add = "Binop(T_i32, Binop_i(Add))"
  let sub = "Binop(T_i32, Binop_i(Sub))"
  let mul = "Binop(T_i32, Binop_i(Mul))"
  let addr = (k : String) => "Local_get(0), \{k}, \{c("4")}, \{mul}, \{add}"
  let load = "Load(T_i32, NONE, 2, 0)"
  let store = "Store(T_i32, NONE, 2, 0)"
  let lt = "Relop(T_i32, Relop_i(Lt(U)))"
  let eq = "Relop(T_i32, Relop_i(Eq))"
  let hm1 = "Local_get(2), \{c("1")}, \{sub}"
  let swap = "[\{addr("Local_get(3)")}, \{load}, Local_set(6), \{addr("Local_get(3)")}, \{addr("Local_get(4)")}, \{load}, \{store}, \{addr("Local_get(4)")}, Local_get(6), \{store}, Local_get(3), \{c("1")}, \{add}, Local_set(3)]"
  let body = "[Local_get(4), \{hm1}, \{eq}, Br_if(1), \{addr("Local_get(4)")}, \{load}, Local_get(5), \{lt}, If(Tbv(NONE), \{swap}, NIL), Local_get(4), \{c("1")}, \{add}, Local_set(4), Br(0)]"
  let code = "[\{addr(hm1)}, \{load}, Local_set(5), Local_get(1), Local_set(3), Local_get(1), Local_set(4), Block(Tbv(NONE), [Loop(Tbv(NONE), \{body})]), \{addr("Local_get(3)")}, \{load}, Local_set(6), \{addr("Local_get(3)")}, Local_get(5), \{store}, \{addr(hm1)}, Local_get(6), \{store}, Local_get(3)]"
  let lw = "List[\{w}]"
  let locals = (i : String, j : String, t : String) => "[\{i_("(p : \{w})")}, \{i_("(lo : \{w})")}, \{i_("(hi : \{w})")}, \{i_(i)}, \{i_(j)}, \{i_("(pv : \{w})")}, \{i_(t)}]"
  let below = "ALL((x : \{w}) => val(x) < val(pv), L)"
  let above = "ALL((x : \{w}) => val(pv) <= val(x), G)"
  let mem = (l : String) => "star(arr(val((p : \{w})), APPEND((A : \{lw}), \{l})), (fp : \{rty})(gs, ms), h)"
  let state = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) =>"
  let sassn = "(vs : List[Value]) => \{state}"
  let inv = "\{state} ∃ i : \{w}, ∃ j : \{w}, ∃ L : \{lw}, ∃ G : \{lw}, ∃ Us : \{lw}, ∃ t : \{w}, lc == \{locals("i", "j", "t")} && LENGTH(A) + LENGTH(L) == val(i) && val(i) + LENGTH(G) == val(j) && val(j) + LENGTH(Us) + 1 == val(hi) && \{below} && \{above} && perm(APPEND(L, APPEND(G, Us)), (Bt : \{lw})) && \{mem("APPEND(L, APPEND(G, APPEND(Us, CONS(pv, (Cs : \{lw})))))")}"
  let after_if = "\{sassn} ∃ i : \{w}, ∃ L : \{lw}, ∃ G : \{lw}, ∃ Us : \{lw}, ∃ t : \{w}, vs == NIL && lc == \{locals("i", "(j : \{w})", "t")} && LENGTH(A) + LENGTH(L) == val(i) && val(i) + LENGTH(G) == val(j) + 1 && val(j) + 1 + LENGTH(Us) + 1 == val(hi) && \{below} && \{above} && perm(APPEND(L, APPEND(G, Us)), Bt) && \{mem("APPEND(L, APPEND(G, APPEND(Us, CONS(pv, Cs))))")}"
  let after_block = "\{sassn} ∃ i : \{w}, ∃ j : \{w}, ∃ L : \{lw}, ∃ G : \{lw}, ∃ t : \{w}, vs == NIL && lc == \{locals("i", "j", "t")} && LENGTH(A) + LENGTH(L) == val(i) && val(i) + LENGTH(G) == val(j) && val(j) + 1 == val(hi) && \{below} && \{above} && perm(APPEND(L, G), Bt) && \{mem("APPEND(L, APPEND(G, CONS(pv, Cs)))")}"
  let post = "\{sassn} ∃ i : \{w}, ∃ L : \{lw}, ∃ G : \{lw}, vs == [\{i_("i")}] && LENGTH(A) + LENGTH(L) == val(i) && \{below} && \{above} && perm(APPEND(L, G), Bt) && LENGTH(L) + LENGTH(G) == LENGTH(Bt) && \{mem("APPEND(L, CONS(pv, APPEND(G, Cs)))")}"
  let z = i_("word(0)")
  let pre = "st(NIL, [\{i_("p")}, \{i_("lo")}, \{i_("hi")}, \{z}, \{z}, \{z}, \{z}], (gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{mem("APPEND(Bt, CONS(pv, Cs))")})"
  let facts = "LENGTH(A) == val(lo) && LENGTH(A) + LENGTH(Bt) + 1 == val(hi) && val(p) + 4 * (val(hi) + LENGTH(Cs)) < 4294967296"
  let part_th = sym_prove(
    "partition_body",
    "∀ p : \{w}, ∀ lo : \{w}, ∀ hi : \{w}, ∀ A : \{lw}, ∀ Bt : \{lw}, ∀ pv : \{w}, ∀ Cs : \{lw}, ∀ fp : \{rty}, \{facts} → sl_triple(\{pre}, \{code}, \{post})",
    [inv],
    partition_vcs(),
    afters=[after_block, after_if],
    rules=[
      "st_const", "st_binop", "st_testop", "st_relop", "st_local_get", "st_local_set", "st_arr_load_at",
      "st_arr_store_at",
    ],
    kind="lemma",
  )
  partition_parts.val = Some((code, pre, post, part_th))
}

///|
/// The partition's code, its precondition and postcondition (as
/// partition_body states them), and partition_body.
let partition_parts : Ref[(String, String, String, @kernel.Thm)?] = Ref::{ val: None }

///|
/// The word facts of a verification condition: hi - 1, i + 1 and j + 1 as
/// numbers, and equations between words as equations of their values.
fn qs_words() -> @tactics.Tactic raise {
  let w = w32
  let fact = (stmt : String, th : String) => @tactics.try_tac(
    have(stmt, seq([@tactics.match_mp_tac(thm(th)), @int.asm_arith_tac])),
  )
  seq([
    fact("val(word_sub((hi : \{w}), word(1))) == val(hi) - 1", "val_pred"),
    fact("val(word_add((i : \{w}), word(1))) == val(i) + 1", "val_succ"),
    fact("val(word_add((i' : \{w}), word(1))) == val(i') + 1", "val_succ"),
    fact("val(word_add((j : \{w}), word(1))) == val(j) + 1", "val_succ"),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@equal.gsym(@words.val_eq()), @words.word_ult_v1(), @arith.not_lt()]))),
    use_eqs(t => eq_of(t, "val(word_")),
  ])
}

///|
/// The partition's verification conditions, in the order sym_prove leaves
/// them.
fn partition_vcs() -> Array[@tactics.Tactic] raise {
  let w = w32
  let l = (x : String) => "(\{x} : List[\{w}])"
  let ex = (ts : Array[String]) => seq(ts.map(t => @tactics.exists_tac(tm(t))))
  let arith = @tactics.try_tac(@int.asm_arith_tac)
  let lengths = [thm("length_list_update"), @lists.length_append(), @lists.length(), thm("length_rot")]
  // an address inside the array
  let bounds = seq([qs_words(), @simp.rewrite_tac(ths(lengths)), arith])
  // the indices i and j as lengths, so el_mid and part_swap apply
  let at = (eqs : Array[String]) => {
    let shown = eqs.map(e => show(tm(e)))
    seq([seq(eqs.map(e => have(e, @int.asm_arith_tac))), use_eqs(t => shown.iter().any(e => show(t) == e))])
  }
  let k_i = "val((i : \{w})) == LENGTH((A : List[\{w}])) + LENGTH((L : List[\{w}]))"
  let k_j = "val((j : \{w})) == LENGTH((A : List[\{w}])) + LENGTH((L : List[\{w}])) + LENGTH((G : List[\{w}]))"
  // U is u :: U2 (the loop goes on)
  let split_u = seq([
    have(
      "∃ u : \{w}, ∃ U2 : List[\{w}], (Us : List[\{w}]) == CONS(u, U2)",
      seq([@tactics.match_mp_tac(thm("nonempty_cons")), @int.asm_arith_tac]),
    ),
    @tactics.first_x_assum(th => @tactics.strip_assume_tac(th)),
    subst_only("Us"),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.append(), @lists.length()]))),
    at([k_i, k_j]),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("el_mid")]))),
  ])
  let finish = seq([
    @simp.rewrite_tac(
      ths(
        [@equal.gsym(@lists.append_assoc()), @lists.append(), @lists.all_append(), @lists.all(), thm("all_rot")] +
        lengths,
      ),
    ),
    @simp.asm_rewrite_tac(ths([])),
    arith,
  ])
  [
    bounds,
    // the loop's entry: nothing looked at yet
    seq([
      qs_words(),
      ex(["(NIL : List[\{w}])", "(NIL : List[\{w}])", l("Bt")]),
      have(
        "EL(val((hi : \{w})) - 1, APPEND((A : List[\{w}]), APPEND((Bt : List[\{w}]), CONS((pv : \{w}), (Cs : List[\{w}]))))) == pv",
        seq([
          have("val((hi : \{w})) - 1 == LENGTH((A : List[\{w}])) + LENGTH((Bt : List[\{w}]))", @int.asm_arith_tac),
          @tactics.first_x_assum(th => @simp.rewrite_tac(ths([th]))),
          @tactics.match_accept_tac(thm("el_mid2")),
        ]),
      ),
      @simp.asm_rewrite_tac(ths([@lists.append(), @lists.all(), thm("perm_refl"), @lists.length()])),
      arith,
    ]),
    // j = hi - 1: out of the loop, U is empty
    seq([
      qs_words(),
      have("LENGTH((Us : List[\{w}])) == 0", @int.asm_arith_tac),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_eq_nil()]))),
      subst_only("Us"),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.append(), @lists.append_nil()]))),
      ex([l("L"), l("G")]),
      @simp.asm_rewrite_tac(ths([])),
      arith,
    ]),
    bounds,
    bounds,
    bounds,
    bounds,
    bounds,
    // a[j] < pv: it joins L, G's first word goes to G's end
    seq([
      qs_words(),
      split_u,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("part_swap")]))),
      @tactics.first_assum(th => @tactics.assume_tac(@drule.match_mp(thm("perm_move"))(th))),
      ex(["APPEND(\{l("L")}, [(u : \{w})])", "rot(\{l("G")})", l("U2")]),
      finish,
    ]),
    // a[j] >= pv: it joins G
    seq([qs_words(), split_u, ex([l("L"), "APPEND(\{l("G")}, [(u : \{w})])", l("U2")]), finish]),
    // the next j
    seq([qs_words(), ex([l("L'"), l("G'"), l("Us'")]), @simp.asm_rewrite_tac(ths([])), arith]),
    bounds,
    bounds,
    bounds,
    // pv goes between L and G
    seq([
      qs_words(),
      at([k_i, "val((hi : \{w})) - 1 == LENGTH((A : List[\{w}])) + LENGTH((L : List[\{w}])) + LENGTH((G : List[\{w}]))"]),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("part_swap")]))),
      @tactics.first_assum(th => @tactics.assume_tac(@drule.match_mp(thm("perm_rot"))(th))),
      ex([l("L"), "rot(\{l("G")})"]),
      finish,
    ]),
  ]
}

///|
/// The two functions' specs, as texts (for qs_spec and the call sites).
fn qsort_specs() -> (String, String, String, String) {
  let w = w32
  let lw = "List[\{w}]"
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let args = "args == [\{i_("(p : \{w})")}, \{i_("(lo : \{w})")}, \{i_("(hi : \{w})")}]"
  let bound = "val(p) + 4 * (val(hi) + LENGTH((Cs : \{lw}))) < 4294967296"
  let mem = (l : String) => "star(arr(val((p : \{w})), APPEND((A : \{lw}), \{l})), (fp : \{rty})(gs, ms), h)"
  let fargs = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) =>"
  let fres = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) =>"
  let qs_p = "\{fargs} \{args} && LENGTH(A) == val(lo) && LENGTH(A) + LENGTH((B : \{lw})) == val(hi) && \{bound} && \{mem("APPEND(B, Cs)")}"
  let qs_q = "\{fres} res == NIL && (∃ ys : \{lw}, sorted(ys) && perm(ys, B) && LENGTH(ys) == LENGTH(B) && \{mem("APPEND(ys, Cs)")})"
  let pt_p = "\{fargs} \{args} && LENGTH(A) == val(lo) && LENGTH(A) + LENGTH((Bt : \{lw})) + 1 == val(hi) && \{bound} && \{mem("APPEND(Bt, CONS((pv : \{w}), Cs))")}"
  let pt_q = "\{fres} (∃ i : \{w}, ∃ L : \{lw}, ∃ G : \{lw}, res == [\{i_("i")}] && LENGTH(A) + LENGTH(L) == val(i) && ALL((x : \{w}) => val(x) < val(pv), L) && ALL((x : \{w}) => val(pv) <= val(x), G) && perm(APPEND(L, G), Bt) && LENGTH(L) + LENGTH(G) == LENGTH(Bt) && \{mem("APPEND(L, CONS(pv, APPEND(G, Cs)))")})"
  (qs_p, qs_q, pt_p, pt_q)
}

///|
fn prove_quicksort() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let (qs_p, qs_q, pt_p, pt_q) = qsort_specs()
  let qs_vars = "∃ p : \{w}, ∃ lo : \{w}, ∃ hi : \{w}, ∃ A : \{lw}, ∃ B : \{lw}, ∃ Cs : \{lw}, ∃ fp : \{rty}"
  let pt_vars = "∃ p : \{w}, ∃ lo : \{w}, ∃ hi : \{w}, ∃ A : \{lw}, ∃ Bt : \{lw}, ∃ pv : \{w}, ∃ Cs : \{lw}, ∃ fp : \{rty}"
  def(
    "qs_spec",
    "qs_spec((inst : Inst), (a : Num), (P : \{fprop}), (Q : \{fprop})) == ((a == sfunc_ind(inst, 0) && (\{qs_vars}, P == (\{qs_p}) && Q == (\{qs_q}))) || (a == sfunc_ind(inst, 1) && (\{pt_vars}, P == (\{pt_p}) && Q == (\{pt_q}))))",
  )
  let qs_call = lemma(
    "qs_call",
    "∀ inst : Inst, ∀ p : \{w}, ∀ lo : \{w}, ∀ hi : \{w}, ∀ A : \{lw}, ∀ B : \{lw}, ∀ Cs : \{lw}, ∀ fp : \{rty}, qs_spec(inst, sfunc_ind(inst, 0), \{qs_p}, \{qs_q})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("qs_spec")])),
      @tactics.disj1_tac,
      seq(["(p : \{w})", "(lo : \{w})", "(hi : \{w})", "(A : \{lw})", "(B : \{lw})", "(Cs : \{lw})", "(fp : \{rty})"].map(v => @tactics.exists_tac(tm(v)))),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let part_call = lemma(
    "partition_call",
    "∀ inst : Inst, ∀ p : \{w}, ∀ lo : \{w}, ∀ hi : \{w}, ∀ A : \{lw}, ∀ Bt : \{lw}, ∀ pv : \{w}, ∀ Cs : \{lw}, ∀ fp : \{rty}, qs_spec(inst, sfunc_ind(inst, 1), \{pt_p}, \{pt_q})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("qs_spec")])),
      @tactics.disj2_tac,
      seq(["(p : \{w})", "(lo : \{w})", "(hi : \{w})", "(A : \{lw})", "(Bt : \{lw})", "(pv : \{w})", "(Cs : \{lw})", "(fp : \{rty})"].map(v => @tactics.exists_tac(tm(v)))),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  prove_qs_list_lemmas()
  let c = (x : String) => "EConstNum(ConstInt32(word(\{x})))"
  let add = "Binop(T_i32, Binop_i(Add))"
  let sub = "Binop(T_i32, Binop_i(Sub))"
  let lt = "Relop(T_i32, Relop_i(Lt(U)))"
  let code = "[Local_get(2), Local_get(1), \{sub}, \{c("2")}, \{lt}, If(Tbv(NONE), [Return], NIL), Local_get(0), Local_get(1), Local_get(2), Call(1), Local_set(3), Local_get(0), Local_get(1), Local_get(3), Call(0), Local_get(0), Local_get(3), \{c("1")}, \{add}, Local_get(2), Call(0)]"
  let qb = body_post("(\{qs_q})")
  let pb = body_pre("(\{qs_p})", "args", "[V_num(ConstInt32(word(0)))]")
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let after_if = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == [\{i_("p")}, \{i_("lo")}, \{i_("hi")}, \{i_("word(0)")}] && !word_ult(word_sub(hi, lo), word(2)) && star(arr(val(p), APPEND(A, APPEND(B, Cs))), fp(gs, ms), h)"
  let inst = "(inst : Inst)"
  let qs_th = sym_prove(
    "quicksort_body",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{w}, ∀ lo : \{w}, ∀ hi : \{w}, ∀ A : \{lw}, ∀ B : \{lw}, ∀ Cs : \{lw}, ∀ fp : \{rty}, ∀ args : List[Value], sl_triple_g(qs_spec(inst), fs, inst, \{qb}, \{pb}, \{code}, \{qb}, [\{qb}])",
    [],
    quicksort_vcs(),
    afters=[after_if],
    specs=[qs_call, part_call],
    calls=[
      (1, [inst, "(p : \{w})", "(lo : \{w})", "(hi : \{w})", "(A : \{lw})", "BUTLAST((B : \{lw}))", "LAST((B : \{lw}))", "(Cs : \{lw})", "(fp : \{rty})"]),
      (0, [inst, "(p : \{w})", "(lo : \{w})", "(i : \{w})", "(A : \{lw})", "(L : \{lw})", "CONS(LAST((B : \{lw})), APPEND((G : \{lw}), (Cs : \{lw})))", "(fp : \{rty})"]),
      (0, [inst, "(p : \{w})", "word_add((i : \{w}), word(1))", "(hi : \{w})", "APPEND((A : \{lw}), APPEND((ys : \{lw}), [LAST((B : \{lw}))]))", "(G : \{lw})", "(Cs : \{lw})", "(fp : \{rty})"]),
    ],
    rules=["st_const", "st_binop", "st_testop", "st_relop", "st_local_get", "st_local_set"],
    kind="lemma",
  )
  prove_quicksort_specs(code, qs_th, qs_call)
}

///|
/// The partition as a function body: its facts come out of the
/// precondition, and partition_body (call-free code) does the rest.
fn prove_partition_fn() -> @kernel.Thm raise {
  let w = w32
  let lw = "List[\{w}]"
  let (_, _, pt_p, pt_q) = qsort_specs()
  guard partition_parts.val is Some((code, pre, post, part_th)) else { raise Failure("partition_fn") }
  let z = "V_num(ConstInt32(word(0)))"
  let zs = "[\{z}, \{z}, \{z}, \{z}]"
  let qb = body_post("(\{pt_q})")
  let pb = body_pre("(\{pt_p})", "args", zs)
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let facts = "args == [\{i_("(p : \{w})")}, \{i_("(lo : \{w})")}, \{i_("(hi : \{w})")}] && LENGTH((A : \{lw})) == val((lo : \{w})) && LENGTH(A) + LENGTH((Bt : \{lw})) + 1 == val((hi : \{w})) && val(p) + 4 * (val(hi) + LENGTH((Cs : \{lw}))) < 4294967296"
  let r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => star(arr(val(p), APPEND(A, APPEND(Bt, CONS((pv : \{w}), Cs)))), (fp : \{rty})(gs, ms), h)"
  let p2 = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (\{facts}) && st(NIL, APPEND(args, \{zs}), \{r})(vs, lc, gs, ms, h)"
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([thm("st")])),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let stmt = "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{w}, ∀ lo : \{w}, ∀ hi : \{w}, ∀ A : \{lw}, ∀ Bt : \{lw}, ∀ pv : \{w}, ∀ Cs : \{lw}, ∀ fp : \{rty}, ∀ args : List[Value], sl_triple_g(qs_spec(inst), fs, inst, \{qb}, \{pb}, \{code}, \{qb}, [\{qb}])"
  lemma(
    "partition_fn",
    stmt,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(thm("sl_pre_g")),
      @tactics.exists_tac(tm(p2)),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          simple,
          seq([
            @tactics.match_mp_tac(thm("sl_pure_g")),
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            subst_only("args"),
            @simp.rewrite_tac(ths([@lists.append()])),
            @tactics.match_mp_tac(thm("sl_conseq_g")),
            @tactics.exists_tac(tm(pre)),
            @tactics.exists_tac(tm(post)),
            @tactics.exists_tac(tm("[\{qb}]")),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(@list.List([
              solve(seq([
                @tactics.match_mp_tac(thm("sl_triple_g_of")),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    call_free_tac(),
                    seq([
                      @tactics.match_mp_tac(thm("sl_triple_l_of")),
                      @tactics.match_mp_tac(part_th),
                      @simp.asm_rewrite_tac(ths([])),
                    ]),
                  ]),
                ),
              ])),
              solve(simple),
            ])),
          ]),
        ]),
      ),
    ]),
  )
}

///|
/// The specs of qs_spec hold (sl_funs_g), and so the quicksort of an
/// array from a caller.
fn prove_quicksort_specs(qs_code : String, qs_th : @kernel.Thm, qs_call : @kernel.Thm) -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let part_fn = prove_partition_fn()
  guard partition_parts.val is Some((pt_code, _, _, _)) else { raise Failure("quicksort_specs") }
  let i32 = "T_num(T_i32)"
  let tf = "Tf([\{i32}, \{i32}, \{i32}], (NIL : List[Valtype]))"
  let tf1 = "Tf([\{i32}, \{i32}, \{i32}], [\{i32}])"
  let z = "V_num(ConstInt32(word(0)))"
  let natives = "EL(sfunc_ind(inst, 0), fs) == Func_native(inst, \{tf}, [\{i32}], \{qs_code}) && EL(sfunc_ind(inst, 1), fs) == Func_native(inst, \{tf1}, [\{i32}, \{i32}, \{i32}, \{i32}], \{pt_code})"
  let zeros = [@wasm.thm("n_zeros"), @lists.map(), @wasm.thm("bitzero"), @wasm.thm("bitzero_num"), @wasm.thm("those"), @wasm.thm("map_option")]
  let witnesses = (t2 : String, ts : String, code : String, zs : String) => seq(
    ["[\{i32}, \{i32}, \{i32}]", t2, ts, code, zs].map(t => @tactics.exists_tac(tm(t))),
  )
  // the function's body, or its arity
  let parts = (body : @kernel.Thm, vars : Array[String]) => seq([
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([
      solve(@tactics.first_assum(th => @tactics.accept_tac(th))),
      solve(seq([
        @tactics.x_gen_tac(tm("(args : List[Value])")),
        @tactics.accept_tac(@bool.ispecl(@list.List((["(fs : List[Cl])", "(inst : Inst)"] + vars + ["(args : List[Value])"]).map(tm)), body)),
      ])),
      solve(seq([
        @simp.rewrite_tac(ths(zeros)),
        @tactics.repeat_tac(
          seq([@tactics.conv_tac(@equal.changed_conv(@equal.top_depth_conv(x => @ind_types.match_conv(x)))), @simp.rewrite_tac(ths(zeros))]),
        ),
      ])),
      solve(seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(ths([])),
        @tactics.repeat_tac(@tactics.strip_tac),
        @simp.asm_rewrite_tac(ths([@lists.length()])),
      ])),
    ])),
  ])
  let specs = lemma(
    "quicksort_specs",
    "∀ fs : List[Cl], ∀ inst : Inst, \{natives} → (∀ n : Num, specs_ok(n, qs_spec(inst), fs, inst))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("sl_funs_g")),
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("qs_spec")])),
      @tactics.thenl(
        @tactics.repeat_tac(@tactics.strip_tac),
        @list.List([
          seq([subst_vars(), witnesses("(NIL : List[Valtype])", "[\{i32}]", qs_code, "[\{z}]"), parts(qs_th, ["(p : \{w})", "(lo : \{w})", "(hi : \{w})", "(A : \{lw})", "(B : \{lw})", "(Cs : \{lw})", "(fp : \{rty})"])]),
          seq([subst_vars(), witnesses("[\{i32}]", "[\{i32}, \{i32}, \{i32}, \{i32}]", pt_code, "[\{z}, \{z}, \{z}, \{z}]"), parts(part_fn, ["(p : \{w})", "(lo : \{w})", "(hi : \{w})", "(A : \{lw})", "(Bt : \{lw})", "(pv : \{w})", "(Cs : \{lw})", "(fp : \{rty})"])]),
        ]),
      ),
    ]),
  )
  // the caller: the whole array of n words at p
  let i_ = (x : String) => "V_num(ConstInt32(\{x}))"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == APPEND(vs0, [\{i_("p")}, \{i_("word(0)")}, \{i_("n")}]) && lc == lc0 && star(arr(val(p), xs), fp(gs, ms), h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ ys : \{lw}, vs == vs0 && lc == lc0 && sorted(ys) && perm(ys, xs) && star(arr(val(p), ys), fp(gs, ms), h))"
  let call = @equal.beta_rule(
    @bool.ispecl(
      @list.List(["(inst : Inst)", "(p : \{w})", "(word(0) : \{w})", "(n : \{w})", "(NIL : \{lw})", "(xs : \{lw})", "(NIL : \{lw})", "(fp : \{rty})"].map(tm)),
      qs_call,
    ),
  )
  let (_, cargs) = @basics.strip_comb(@kernel.concl(call))
  let cargs = cargs.to_array()
  let pp = cargs[cargs.length() - 2]
  let qq = cargs[cargs.length() - 1]
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([@lists.append(), @lists.append_nil(), @lists.length(), @words.val_word_0(), @arith.add_clauses()])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([@lists.append(), @lists.append_nil(), @arith.add_clauses()])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let th = @tactics.prove(
    tm(
      "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{w}, ∀ n : \{w}, ∀ xs : \{lw}, ∀ fp : \{rty}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], \{natives} && LENGTH(xs) == val(n) && val(p) + 4 * val(n) < 4294967296 → sl_triple_m(fs, inst, \{pre}, [Call(0)], \{post}, NIL)",
    ),
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
      @tactics.exists_tac(tm("qs_spec((inst : Inst))")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@tactics.match_mp_tac(specs), @simp.asm_rewrite_tac(ths([]))]),
          seq([
            @tactics.match_mp_tac(thm("sl_conseq_g")),
            @tactics.exists_tac(with_spec(call_pre("(Pv : \{fprop})", "(vs0 : List[Value])", "(lc0 : List[Value])"), "Pv", pp)),
            @tactics.exists_tac(with_spec(call_post("(Qv : \{fprop})", "(vs0 : List[Value])", "(lc0 : List[Value])"), "Qv", qq)),
            @tactics.exists_tac(tm("(NIL : List[\{sassn}])")),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(@list.List([
              solve(seq([@tactics.match_mp_tac(thm("sl_call_g")), @tactics.accept_tac(call)])),
              solve(simple),
            ])),
          ]),
        ]),
      ),
    ]),
  )
  record("example_quicksort", th, kind="example")
}

///|
/// What quicksort's verification conditions need about lists.
fn prove_qs_list_lemmas() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let sorted_rws = [
    thm("sorted"),
    @lists.pairwise_append(),
    @lists.pairwise(),
    @equal.gsym(@lists.all_mem()),
    @lists.mem_append(),
    @lists.mem(),
  ]
  let _ = lemma(
    "qs_split",
    "∀ hi : \{w}, ∀ lo : \{w}, ∀ A : \{lw}, ∀ B : \{lw}, LENGTH(A) == val(lo) && LENGTH(A) + LENGTH(B) == val(hi) → (word_ult(word_sub(hi, lo), word(2)) == (LENGTH(B) < 2))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      have("val((lo : \{w})) <= val((hi : \{w}))", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(ths([@words.word_ult_v1(), @words.val_word_sub_cases(), @words.val_word(), @words.dimindex_32()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @int.asm_arith_tac,
    ]),
  )
  let b_cases = (v : String) => @tactics.struct_cases_tac(@bool.ispec(tm("(\{v} : \{lw})"), @lists.list_cases()))
  let _ = lemma(
    "sorted_short",
    "∀ B : \{lw}, LENGTH(B) < 2 → sorted(B)",
    seq([
      @tactics.gen_tac,
      b_cases("B"),
      @simp.rewrite_tac(ths([thm("sorted"), @lists.pairwise(), @lists.length(), @lists.all()])),
      @tactics.try_tac(b_cases("t")),
      @simp.rewrite_tac(ths([@lists.pairwise(), @lists.length(), @lists.all()])),
      @tactics.try_tac(@int.arith_tac),
    ]),
  )
  let _ = lemma(
    "mem_count",
    "∀ x : \{w}, ∀ l : \{lw}, MEM(x, l) == (0 < LENGTH(FILTER((z : \{w}) => z == x, l)))",
    seq([
      @tactics.gen_tac,
      @lists.list_induct_tac,
      @simp.rewrite_tac(ths([@lists.mem(), @lists.filter(), @lists.length()])),
      @tactics.try_tac(seq([
        g => @class.cond_cases_tac(g),
        @simp.asm_rewrite_tac(ths([@lists.length()])),
      ])),
      @tactics.try_tac(@int.arith_tac),
    ]),
  )
  let _ = lemma(
    "perm_all",
    "∀ P : (\{w}) -> Bool, ∀ xs : \{lw}, ∀ ys : \{lw}, perm(xs, ys) && ALL(P, ys) → ALL(P, xs)",
    seq([
      @simp.rewrite_tac(ths([thm("perm"), @equal.gsym(@lists.all_mem()), thm("mem_count")])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sorted_join",
    "∀ ys : \{lw}, ∀ pv : \{w}, ∀ ys2 : \{lw}, sorted(ys) && sorted(ys2) && ALL((x : \{w}) => val(x) < val(pv), ys) && ALL((x : \{w}) => val(pv) <= val(x), ys2) → sorted(APPEND(ys, CONS(pv, ys2)))",
    seq([
      @simp.rewrite_tac(ths(sorted_rws)),
      @meson.meson_tac(
        ths([arith("∀ a : Num, ∀ b : Num, a < b → a <= b"), arith("∀ a : Num, ∀ b : Num, ∀ c : Num, a < b && b <= c → a <= c")]),
      ),
    ]),
  )
  let _ = lemma(
    "perm_join",
    "∀ ys : \{lw}, ∀ L : \{lw}, ∀ ys2 : \{lw}, ∀ G : \{lw}, ∀ Bt : \{lw}, ∀ pv : \{w}, perm(ys, L) && perm(ys2, G) && perm(APPEND(L, G), Bt) → perm(APPEND(ys, CONS(pv, ys2)), APPEND(Bt, [pv]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("perm"), @lists.filter_append(), @lists.length_append(), @lists.filter(), @lists.length()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      seq(
        ["ys", "ys2", "L"].map(_ => @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(y : \{w})"), th)))),
      ),
      @class.asm_cases_tac(tm("(pv : \{w}) == (y : \{w})")),
      @simp.asm_rewrite_tac(ths([@lists.length(), @lists.length_append(), @lists.filter()])),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "butlast_cons",
    "∀ B : \{lw}, ∀ Cs : \{lw}, !(B == NIL) → APPEND(BUTLAST(B), CONS(LAST(B), Cs)) == APPEND(B, Cs) && LENGTH(BUTLAST(B)) + 1 == LENGTH(B) && APPEND(BUTLAST(B), [LAST(B)]) == B",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.assume_tac(@drule.match_mp(@lists.append_butlast_last())(th))),
      @tactics.first_assum(th => @tactics.assume_tac(@equal.ap_term(tm("(LENGTH : (\{lw}) -> Num)"), th))),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_append(), @lists.length()]))),
      @simp.once_rewrite_tac(ths([cons_as_snoc()])),
      @simp.asm_rewrite_tac(ths([@lists.append_nil()])),
      @int.asm_arith_tac,
    ]),
  )
}

///|
/// APPEND(l, CONS(x, m)) is APPEND(APPEND(l, [x]), m) (not a rewrite to
/// repeat: its right side matches its left).
fn cons_as_snoc() -> @kernel.Thm raise {
  @tactics.prove(
    tm("∀ l : List[A], ∀ x : A, ∀ m : List[A], APPEND(l, CONS(x, m)) == APPEND(APPEND(l, [x]), m)"),
    @simp.rewrite_tac(ths([@equal.gsym(@lists.append_assoc()), @lists.append()])),
  )
}

///|
/// Quicksort's verification conditions, in the order sym_prove leaves them.
fn quicksort_vcs() -> Array[@tactics.Tactic] raise {
  let w = w32
  let lw = "List[\{w}]"
  let l = (x : String) => "(\{x} : \{lw})"
  let v = (x : String) => "(\{x} : \{w})"
  // the segment's length: < 2 (returned) or >= 2
  let segment = seq([
    @tactics.mp_tac(@bool.ispecl(@list.List([v("hi"), v("lo"), l("A"), l("B")].map(tm)), thm("qs_split"))),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.disch_tac,
  ])
  // B is BUTLAST(B) ++ [LAST(B)]
  let split_b = seq([
    segment,
    have("!((B : \{lw}) == NIL)", seq([@tactics.disch_tac, subst_vars(), @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length()]))), @int.asm_arith_tac])),
    @tactics.first_assum(th => @tactics.strip_assume_tac(@bool.spec(tm(l("Cs")), @drule.match_mp(@bool.spec(tm(l("B")), thm("butlast_cons")))(th)))),
  ])
  let lengths = seq([
    @simp.rewrite_tac(ths([@lists.length_append(), @lists.length()])),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_append(), @lists.length()]))),
    @int.asm_arith_tac,
  ])
  [
    // the segment has fewer than 2 words: it is sorted
    seq([
      segment,
      @tactics.exists_tac(tm(l("B"))),
      have("sorted((B : \{lw}))", seq([@tactics.match_mp_tac(thm("sorted_short")), @tactics.first_assum(th => @tactics.accept_tac(th))])),
      @simp.asm_rewrite_tac(ths([thm("perm_refl")])),
    ]),
    // the partition's precondition: B is BUTLAST(B) ++ [LAST(B)]
    seq([split_b, @simp.asm_rewrite_tac(ths([])), @int.asm_arith_tac]),
    // the left part's bound
    seq([split_b, lengths]),
    // the right part starts after the pivot
    seq([
      split_b,
      have("val(word_add((i : \{w}), word(1))) == val(i) + 1", seq([@tactics.match_mp_tac(thm("val_succ")), lengths])),
      @simp.asm_rewrite_tac(ths([])),
      lengths,
    ]),
    // both parts sorted, around the pivot
    seq([
      split_b,
      @tactics.exists_tac(tm("APPEND(\{l("ys")}, CONS(LAST(\{l("B")}), \{l("ys'")}))")),
      have(
        "sorted(APPEND(\{l("ys")}, CONS(LAST(\{l("B")}), \{l("ys'")})))",
        seq([@tactics.match_mp_tac(thm("sorted_join")), @meson.asm_meson_tac(ths([thm("perm_all")]))]),
      ),
      have(
        "perm(APPEND(\{l("ys")}, CONS(LAST(\{l("B")}), \{l("ys'")})), APPEND(BUTLAST(B), [LAST(B)]))",
        seq([@tactics.match_mp_tac(thm("perm_join")), @meson.asm_meson_tac(ths([]))]),
      ),
      // BUTLAST(B) ++ [LAST(B)] is B
      @tactics.first_assum(th => if show(@kernel.concl(th)).has_prefix("APPEND(BUTLAST") && show(@kernel.concl(th)).contains("[LAST") {
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th])))
      } else {
        @tactics.no_tac
      }),
      @simp.asm_rewrite_tac(ths([@equal.gsym(@lists.append_assoc()), @lists.append()])),
      lengths,
    ]),
  ]
}
