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
// facts are lemmas (asum_addr, asum_step, asum_exit, asum_entry,
// asum_none); the proof has example_fill's shape.

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
  let _ = lemma(
    "wasm_bool_zero",
    "∀ b : Bool, (wasm_bool(b) == word(0)) == !b",
    seq([
      @tactics.gen_tac,
      @class.bool_cases_tac(tm("(b : Bool)")),
      @simp.rewrite_tac(
        ths([@wasm.thm("wasm_bool"), @equal.gsym(@words.val_eq()), @words.val_word_1(), @words.val_word_0(), arith("!(1 == 0)")]),
      ),
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
  let nil = "(NIL : List[Value])"
  let vs0 = "(vs0 : List[Value])"
  let p = "(p : \{w})"
  let n = "(n : \{w})"
  let i = "(i : \{w})"
  let xs = "(xs : List[\{w}])"
  let ys = "(ys : List[\{w}])"
  let y = "(y : \{w})"
  let zs = "(zs : List[\{w}])"
  let fp = "(fp : \{rty})"
  let array = (l : String) => "(gs : List[Value]) => star(arr(val(\{p}), \{l}), \{fp}(gs))"
  let a_split = array("APPEND(\{ys}, CONS(\{y}, \{zs}))")
  let a_xs = array(xs)
  let acc = "wsum(\{ys})"
  let acc1 = "word_add(wsum(\{ys}), \{y})"
  let i1 = "word_add(\{i}, word(1))"
  let k = "word_add(\{p}, word_mul(\{i}, word(4)))"
  let l0 = "[\{i_(p)}, \{i_(n)}, \{i_(i)}, \{i_(acc)}]"
  let l1 = "[\{i_(p)}, \{i_(n)}, \{i_(i)}, \{i_(acc1)}]"
  let l2 = "[\{i_(p)}, \{i_(n)}, \{i_(i1)}, \{i_(acc1)}]"
  let lt = "Relop_i(Lt(U))"
  let body_code = "[Local_get(3), Local_get(0), Local_get(2), EConstNum(ConstInt32(word(4))), Binop(T_i32, Binop_i(Mul)), Binop(T_i32, Binop_i(Add)), Load(T_i32, NONE, 2, 0), Binop(T_i32, Binop_i(Add)), Local_set(3), Local_get(2), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Add)), Local_set(2), Local_get(2), Local_get(1), Relop(T_i32, \{lt}), Br_if(0)]"
  let length = tm("LENGTH(\{xs}) == val(\{n})")
  let bound = tm("val(\{p}) + 4 * val(\{n}) < 4294967296")
  let linv = "(lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => ∃ i : \{w}, ∃ ys : List[\{w}], ∃ y : \{w}, ∃ zs : List[\{w}], lc == [\{i_(p)}, \{i_(n)}, \{i_("i")}, \{i_("wsum(ys)")}] && \{xs} == APPEND(ys, CONS(y, zs)) && LENGTH(ys) == val(i) && star(arr(val(\{p}), APPEND(ys, CONS(y, zs))), \{fp}(gs), h)"
  let done = "st(\{nil}, [\{i_(p)}, \{i_(n)}, \{i_(n)}, \{i_("wsum(\{xs})")}], \{a_xs})"
  let no_br = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => false"
  let loop_rule = beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), tm(body_code), tm(linv), tm(done), tm("[\{no_br}]"), tm(nil)]),
      thm("sl_loop"),
    ),
  )
  let (_, premise_args) = @basics.strip_comb(@kernel.rand(@kernel.rator(@kernel.concl(loop_rule))))
  let lb = premise_args.to_array()[0]
  let labels = premise_args.to_array()[3]
  let facts = [tm("\{xs} == APPEND(\{ys}, CONS(\{y}, \{zs}))"), tm("LENGTH(\{ys}) == val(\{i})")]
  let shape_args = @list.List([p, n, i, xs, ys, y, zs].map(tm))
  // the load of the word at p + 4i
  let load = @bool.ispecl(
    @list.List([ "[\{i_(acc)}]", l0, "val(\{p})", ys, y, zs, fp, k, "2", "0"].map(tm)),
    thm("st_arr_load"),
  )
  let load = discharge(load, ant => under(
    [length, bound] + facts,
    ant,
    seq([
      @tactics.match_mp_tac(@bool.ispecl(shape_args, thm("asum_addr"))),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  ))
  let steps = [
    inst("st_local_get", [nil, l0, a_split, "3"]),
    inst("st_local_get", ["[\{i_(acc)}]", l0, a_split, "0"]),
    inst("st_local_get", ["[\{i_(acc)}, \{i_(p)}]", l0, a_split, "2"]),
    inst("st_const", ["[\{i_(acc)}, \{i_(p)}, \{i_(i)}]", l0, a_split, "ConstInt32(word(4))"]),
    inst("st_binop", ["[\{i_(acc)}, \{i_(p)}]", l0, a_split, "T_i32", "Binop_i(Mul)", "ConstInt32(\{i})", "ConstInt32(word(4))", "ConstInt32(word_mul(\{i}, word(4)))"]),
    inst("st_binop", ["[\{i_(acc)}]", l0, a_split, "T_i32", "Binop_i(Add)", "ConstInt32(\{p})", "ConstInt32(word_mul(\{i}, word(4)))", "ConstInt32(\{k})"]),
    norm(load),
    inst("st_binop", [nil, l0, a_split, "T_i32", "Binop_i(Add)", "ConstInt32(\{acc})", "ConstInt32(\{y})", "ConstInt32(\{acc1})"]),
    inst("st_local_set", [nil, l0, a_split, "3", "ConstInt32(\{acc1})"]),
    inst("st_local_get", [nil, l1, a_split, "2"]),
    inst("st_const", ["[\{i_(i)}]", l1, a_split, "ConstInt32(word(1))"]),
    inst("st_binop", [nil, l1, a_split, "T_i32", "Binop_i(Add)", "ConstInt32(\{i})", "ConstInt32(word(1))", "ConstInt32(\{i1})"]),
    inst("st_local_set", [nil, l1, a_split, "2", "ConstInt32(\{i1})"]),
    inst("st_local_get", [nil, l2, a_split, "2"]),
    inst("st_local_get", ["[\{i_(i1)}]", l2, a_split, "1"]),
    inst("st_relop", [nil, l2, a_split, "T_i32", lt, "ConstInt32(\{i1})", "ConstInt32(\{n})"]),
  ]
  let mut straight = steps[0]
  for s in 1..<steps.length() {
    straight = glue(straight, steps[s])
  }
  // br_if 0 on i + 1 < n: back with the invariant (asum_step), or out
  // (asum_exit)
  let cond = "wasm_bool(word_ult(\{i1}, \{n}))"
  let br_rule = @bool.ispecl(@list.List([tm("0"), labels]), thm("sl_br"))
  let (br_pre, _, br_post, _) = triple_l_terms(@kernel.rand(@kernel.concl(br_rule)))
  let br_if = norm(
    @bool.ispecl(
      @list.List([tm("st(\{nil}, \{l2}, \{a_split})"), tm(done), labels, tm("0"), tm(cond)]),
      thm("sl_br_if"),
    ),
  )
  let step = @bool.ispecl(shape_args, thm("asum_step"))
  let exit = @bool.ispecl(shape_args, thm("asum_exit"))
  let br_if = discharge(br_if, ant => under(
    [length] + facts,
    ant,
    seq([
      @simp.rewrite_tac(ths([thm("wasm_bool_zero")])),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.disch_tac,
            // the step's facts, without rewriting the goal (its labels hold xs)
            @tactics.thenl(
              @tactics.subgoal_then(@kernel.rand(@kernel.concl(step)), th => @tactics.strip_assume_tac(th)),
              @list.List([seq([@tactics.match_mp_tac(step), @simp.asm_rewrite_tac(ths([]))]), @tactics.all_tac]),
            ),
            // zs is y2 :: zs2 (only that: xs is in the labels, and stays)
            @tactics.first_x_assum(@tactics.subst_var_tac),
            @tactics.match_mp_tac(thm("sl_conseq_l")),
            @tactics.exists_tac(br_pre),
            @tactics.exists_tac(br_post),
            @tactics.exists_tac(labels),
            @tactics.thenl(
              @tactics.repeat_tac(@tactics.conj_tac),
              @list.List([
                seq([
                  @tactics.repeat_tac(@tactics.gen_tac),
                  @simp.rewrite_tac(ths([thm("st")])),
                  @tactics.repeat_tac(@tactics.strip_tac),
                  subst_vars(),
                  @tactics.exists_tac(tm(nil)),
                  @tactics.exists_tac(tm(nil)),
                  @simp.rewrite_tac(ths([@lists.append(), @lists.el_cons()])),
                  @tactics.conv_tac(@calc_num.num_reduce_conv),
                  @simp.rewrite_tac(ths([])),
                  @tactics.exists_tac(tm(i1)),
                  @tactics.exists_tac(tm("APPEND(\{ys}, [\{y}])")),
                  @tactics.exists_tac(tm("(y2 : \{w})")),
                  @tactics.exists_tac(tm("(zs2 : List[\{w}])")),
                  @simp.asm_rewrite_tac(ths([thm("wsum_snoc"), @equal.gsym(@lists.append_assoc()), @lists.append()])),
                ]),
                seq([
                  @tactics.match_mp_tac(br_rule),
                  @simp.rewrite_tac(ths([@lists.length(), arith("∀ n : Num, 0 < SUC(n)")])),
                ]),
                @simp.rewrite_tac(ths([])),
                @simp.rewrite_tac(ths([])),
                seq([@tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))]),
              ]),
            ),
          ]),
          seq([
            @tactics.disch_tac,
            @tactics.mp_tac(exit),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.strip_tac,
            ent_tac(),
          ]),
        ]),
      ),
    ]),
  ))
  let body = glue(with_labels(straight, labels), br_if, rule="sl_seq_l")
  let facts_conj = @bool.list_mk_conj(@list.List(facts))
  let body = under(
    [length, bound],
    @bool.mk_imp(facts_conj, @kernel.concl(body)),
    seq([@tactics.disch_then(th => @tactics.strip_assume_tac(th)), @tactics.accept_tac(body)]),
  )
  let body = beta(@drule.match_mp(thm("sl_pure_l"))(body))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(zs), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(y), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(ys), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(i), body)))
  let (_, _, body_post, _) = triple_l_parts(body)
  let body = conseq_l(body, lb, body_post, ent_tac(), hyps=[length, bound])
  let looped = @bool.mp(loop_rule, body)
  // the block around the loop (0 < n), the empty block (n = 0), the if
  let (loop_pre, loop_code, loop_post, _) = triple_l_parts(looped)
  let start = tm("st(\{vs0}, [\{i_(p)}, \{i_(n)}, \{i_("word(0)")}, \{i_("word(0)")}], \{a_xs})")
  let finish = tm("st(\{vs0}, [\{i_(p)}, \{i_(n)}, \{i_(n)}, \{i_("wsum(\{xs})")}], \{a_xs})")
  let block_rule = (code : @kernel.Term, pb : @kernel.Term, qb : @kernel.Term) => beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), code, pb, qb, tm(no_br), tm("(NIL : List[\{sassn}])"), tm(vs0)]),
      thm("sl_block"),
    ),
  )
  let nonzero = @bool.mp(block_rule(loop_code, loop_pre, loop_post), looped)
  let some = tm("word_ult(word(0), \{n})")
  let entry = @bool.ispecl(@list.List([tm(n), tm(xs)]), thm("asum_entry"))
  let nonzero = conseq_l(
    nonzero,
    start,
    finish,
    seq([
      // xs is y :: zs, none read yet
      @tactics.mp_tac(entry),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.strip_tac,
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("st"), @lists.append(), @lists.append_nil()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([])),
      @tactics.try_tac(seq([
        @tactics.exists_tac(tm("(word(0) : \{w})")),
        @tactics.exists_tac(tm("(NIL : List[\{w}])")),
        @tactics.exists_tac(tm(y)),
        @tactics.exists_tac(tm(zs)),
      ])),
      @simp.asm_rewrite_tac(
        ths([thm("wsum"), @lists.append(), @lists.append_nil(), @lists.length(), @words.val_word_0()]),
      ),
    ]),
    hyps=[some, length, bound],
  )
  let empty = tm("st(\{nil}, [\{i_(p)}, \{i_(n)}, \{i_("word(0)")}, \{i_("word(0)")}], \{a_xs})")
  let zero = block_rule(tm("(NIL : List[B_e])"), empty, empty)
  let zero = @bool.mp(zero, @bool.ispecl(@list.List([empty, tm("[\{no_br}]")]), thm("sl_nil_l")))
  let none = @bool.ispecl(@list.List([tm(n), tm(xs)]), thm("asum_none"))
  let zero = conseq_l(
    zero,
    start,
    finish,
    seq([
      @tactics.mp_tac(none),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.strip_tac,
      subst_vars(),
      ent_tac(rws=[thm("wsum")]),
    ]),
    hyps=[@bool.mk_neg(some), length],
  )
  let if_rule = norm(
    @bool.ispecl(
      @list.List([
        start,
        finish,
        tm("(NIL : List[\{sassn}])"),
        tm("Tbv((NONE : Option[Valtype]))"),
        tm("[Loop(Tbv((NONE : Option[Valtype])), \{body_code})]"),
        tm("(NIL : List[B_e])"),
        tm("wasm_bool(word_ult(word(0), \{n}))"),
      ]),
      thm("sl_if"),
    ),
  )
  let if_rule = discharge(if_rule, ant => under(
    [length, bound],
    ant,
    seq([
      @simp.rewrite_tac(ths([thm("wasm_bool_zero")])),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@tactics.disch_tac, @tactics.accept_tac(nonzero)]),
          seq([@tactics.disch_tac, @tactics.accept_tac(zero)]),
        ]),
      ),
    ]),
  ))
  let l_start = "[\{i_(p)}, \{i_(n)}, \{i_("word(0)")}, \{i_("word(0)")}]"
  let start_steps = [
    inst("st_local_get", [vs0, l_start, a_xs, "2"]),
    inst("st_local_get", ["APPEND(\{vs0}, [\{i_("word(0)")}])", l_start, a_xs, "1"]),
    inst("st_relop", [vs0, l_start, a_xs, "T_i32", lt, "ConstInt32(word(0))", "ConstInt32(\{n})"]),
  ]
  let mut start_code = start_steps[0]
  for s in 1..<start_steps.length() {
    start_code = glue(start_code, start_steps[s])
  }
  let all = glue(with_labels(start_code, tm("(NIL : List[\{sassn}])")), if_rule, rule="sl_seq_l")
  let all = @drule.match_mp(thm("sl_triple_of_l"))(all)
  let all = under(
    [],
    @bool.mk_imp(@bool.mk_conj(length, bound), @kernel.concl(all)),
    seq([@tactics.disch_then(th => @tactics.strip_assume_tac(th)), @tactics.accept_tac(all)]),
  )
  record("example_array_sum", @bool.gen_all(all), kind="example")
}
