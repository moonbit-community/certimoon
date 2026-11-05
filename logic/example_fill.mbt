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
// is (m - c) copies of x, then y :: zs (c words still to write). The
// arithmetic and list facts are lemmas (fill_entry, fill_step,
// fill_exit); the proof has the shape of example_sum's.

///|
/// `goal`, proved by `tac` with `hyps` as assumptions; the theorem keeps
/// them as hypotheses.
fn under(
  hyps : Array[@kernel.Term],
  goal : @kernel.Term,
  tac : @tactics.Tactic,
) -> @kernel.Thm raise {
  let mut g = goal
  for k = hyps.length() - 1; k >= 0; k = k - 1 {
    g = @bool.mk_imp(hyps[k], g)
  }
  let disch = hyps.map(_ => @tactics.disch_then(th => @tactics.strip_assume_tac(th)))
  let mut th = @tactics.prove(g, seq(disch + [tac]))
  for h in hyps {
    th = @bool.mp(th, @kernel.assume_rule(h))
  }
  th
}

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
  let nil = "(NIL : List[Value])"
  let vs0 = "(vs0 : List[Value])"
  let p0 = "(p0 : \{w})"
  let m = "(m : \{w})"
  let x = "(x : \{w})"
  let p = "(p : \{w})"
  let c = "(c : \{w})"
  let y = "(y : \{w})"
  let zs = "(zs : List[\{w}])"
  let fp = "(fp : \{rty})"
  // the array at p0, as a state's R (with η done, as norm leaves it)
  let array = (xs : String) => "(gs : List[Value]) => (ms : Num) => star(arr(val(\{p0}), \{xs}), \{fp}(gs, ms))"
  let written = "REPLICATE(val(\{m}) - val(\{c}), \{x})"
  let a_body = array("APPEND(\{written}, CONS(\{y}, \{zs}))")
  let a_after = array("APPEND(\{written}, CONS(\{x}, \{zs}))")
  let a_final = array("REPLICATE(val(\{m}), \{x})")
  let p4 = "word_add(\{p}, word(4))"
  let c1 = "word_sub(\{c}, word(1))"
  let l0 = "[\{i(p)}, \{i(c)}]"
  let l1 = "[\{i(p4)}, \{i(c)}]"
  let l2 = "[\{i(p4)}, \{i(c1)}]"
  let body_code = "[Local_get(0), EConstNum(ConstInt32(\{x})), Store(T_i32, NONE, 2, 0), Local_get(0), EConstNum(ConstInt32(word(4))), Binop(T_i32, Binop_i(Add)), Local_set(0), Local_get(1), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Sub)), Local_set(1), Local_get(1), Br_if(0)]"
  let bound = tm("val(\{p0}) + 4 * val(\{m}) < 4294967296")
  let linv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ p : \{w}, ∃ c : \{w}, ∃ y : \{w}, ∃ zs : List[\{w}], lc == [\{i("p")}, \{i("c")}] && !(c == word(0)) && val(p) == val(\{p0}) + 4 * (val(\{m}) - val(c)) && val(c) <= val(\{m}) && SUC(LENGTH(zs)) == val(c) && star(arr(val(\{p0}), APPEND(REPLICATE(val(\{m}) - val(c), \{x}), CONS(y, zs))), \{fp}(gs, ms), h)"
  let done = "st(\{nil}, [\{i("word_add(\{p0}, word(4 * val(\{m})))")}, \{i("word(0)")}], \{a_final})"
  let no_br = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => false"
  let loop_rule = beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), tm(body_code), tm(linv), tm(done), tm("[\{no_br}]"), tm(nil)]),
      thm("sl_loop"),
    ),
  )
  let (_, premise_args) = @basics.strip_comb(@kernel.rand(@kernel.rator(@kernel.concl(loop_rule))))
  let lb = premise_args.to_array()[0]
  let labels = premise_args.to_array()[3]
  // the facts the invariant gives about p, c and zs
  let facts = [
    tm("!(\{c} == word(0))"),
    tm("val(\{p}) == val(\{p0}) + 4 * (val(\{m}) - val(\{c}))"),
    tm("val(\{c}) <= val(\{m})"),
    tm("SUC(LENGTH(\{zs})) == val(\{c})"),
  ]
  // the element written is at p
  let store = @bool.ispecl(
    @list.List(
      [nil, l0, "val(\{p0})", written, y, zs, fp, p, "2", "0", x].map(tm),
    ),
    thm("st_arr_store"),
  )
  let store = discharge(store, ant => under(
    facts,
    ant,
    @simp.asm_rewrite_tac(ths([@lists.length_replicate(), @arith.add_clauses()])),
  ))
  let steps = [
    inst("st_local_get", [nil, l0, a_body, "0"]),
    inst("st_const", ["[\{i(p)}]", l0, a_body, "ConstInt32(\{x})"]),
    norm(store),
    inst("st_local_get", [nil, l0, a_after, "0"]),
    inst("st_const", ["[\{i(p)}]", l0, a_after, "ConstInt32(word(4))"]),
    inst("st_binop", [nil, l0, a_after, "T_i32", "Binop_i(Add)", "ConstInt32(\{p})", "ConstInt32(word(4))", "ConstInt32(\{p4})"]),
    inst("st_local_set", [nil, l0, a_after, "0", "ConstInt32(\{p4})"]),
    inst("st_local_get", [nil, l1, a_after, "1"]),
    inst("st_const", ["[\{i(c)}]", l1, a_after, "ConstInt32(word(1))"]),
    inst("st_binop", [nil, l1, a_after, "T_i32", "Binop_i(Sub)", "ConstInt32(\{c})", "ConstInt32(word(1))", "ConstInt32(\{c1})"]),
    inst("st_local_set", [nil, l1, a_after, "1", "ConstInt32(\{c1})"]),
    inst("st_local_get", [nil, l2, a_after, "1"]),
  ]
  let mut straight = steps[0]
  for k in 1..<steps.length() {
    straight = glue(straight, steps[k])
  }
  // br_if 0: back with the invariant (fill_step), or out (fill_exit)
  let br_rule = @bool.ispecl(@list.List([tm("0"), labels]), thm("sl_br"))
  let (br_pre, _, br_post, _) = triple_l_terms(@kernel.rand(@kernel.concl(br_rule)))
  let br_if = norm(
    @bool.ispecl(
      @list.List([tm("st(\{nil}, \{l2}, \{a_after})"), tm(done), labels, tm("0"), tm(c1)]),
      thm("sl_br_if"),
    ),
  )
  let lemma_args = @list.List([p0, m, p, c, x, zs].map(tm))
  let step = @bool.ispecl(lemma_args, thm("fill_step"))
  let exit = @bool.ispecl(lemma_args, thm("fill_exit"))
  let br_if = discharge(br_if, ant => under(
    [bound] + facts,
    ant,
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        seq([
          @tactics.disch_tac,
          @tactics.mp_tac(step),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
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
                @tactics.exists_tac(tm(p4)),
                @tactics.exists_tac(tm(c1)),
                @tactics.exists_tac(tm("(y2 : \{w})")),
                @tactics.exists_tac(tm("(zs2 : List[\{w}])")),
                @simp.asm_rewrite_tac(ths([])),
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
  ))
  let body = glue(with_labels(straight, labels), br_if, rule="sl_seq_l")
  let facts_conj = @bool.list_mk_conj(@list.List(facts))
  let body = under(
    [bound],
    @bool.mk_imp(facts_conj, @kernel.concl(body)),
    seq([@tactics.disch_then(th => @tactics.strip_assume_tac(th)), @tactics.accept_tac(body)]),
  )
  let body = beta(@drule.match_mp(thm("sl_pure_l"))(body))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(zs), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(y), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(c), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(p), body)))
  let (_, _, body_post, _) = triple_l_parts(body)
  let body = conseq_l(body, lb, body_post, ent_tac(), hyps=[bound])
  let looped = @bool.mp(loop_rule, body)
  // the block around the loop (m ≠ 0), the empty block (m = 0), the if
  let (loop_pre, loop_code, loop_post, _) = triple_l_parts(looped)
  let ys = "(ys : List[\{w}])"
  let start = tm("st(\{vs0}, [\{i(p0)}, \{i(m)}], \{array(ys)})")
  let finish = tm("st(\{vs0}, [\{i("word_add(\{p0}, word(4 * val(\{m})))")}, \{i("word(0)")}], \{a_final})")
  let length = tm("LENGTH(\{ys}) == val(\{m})")
  let block_rule = (code : @kernel.Term, pb : @kernel.Term, qb : @kernel.Term) => beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), code, pb, qb, tm(no_br), tm("(NIL : List[\{sassn}])"), tm(vs0)]),
      thm("sl_block"),
    ),
  )
  let nonzero = @bool.mp(block_rule(loop_code, loop_pre, loop_post), looped)
  let nz = tm("!(\{m} == word(0))")
  let entry = @bool.ispecl(@list.List([tm(m), tm(ys)]), thm("fill_entry"))
  let nonzero = conseq_l(
    nonzero,
    start,
    finish,
    seq([
      // ys is y :: zs, all still to write
      @tactics.mp_tac(entry),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.strip_tac,
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("st"), @lists.append(), @lists.append_nil()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([])),
      @tactics.try_tac(seq([
        @tactics.exists_tac(tm(p0)),
        @tactics.exists_tac(tm(m)),
        @tactics.exists_tac(tm("(y : \{w})")),
        @tactics.exists_tac(tm("(zs : List[\{w}])")),
      ])),
      @simp.asm_rewrite_tac(
        ths([arith("∀ n : Num, n - n == 0"), @arith.mult_clauses(), @arith.add_clauses(), @lists.replicate(), @lists.append(), @lists.append_nil(), @arith.le_refl()]),
      ),
    ]),
    hyps=[nz, length, bound],
  )
  let empty = tm("st(\{nil}, [\{i(p0)}, \{i(m)}], \{array(ys)})")
  let zero = block_rule(tm("(NIL : List[B_e])"), empty, empty)
  let zero = @bool.mp(zero, @bool.ispecl(@list.List([empty, tm("[\{no_br}]")]), thm("sl_nil_l")))
  let z = tm("\{m} == word(0)")
  let zero = conseq_l(
    zero,
    start,
    finish,
    seq([
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.val_word_0(), @lists.length_eq_nil()]))),
      subst_vars(),
      ent_tac(rws=[@words.val_word_0(), @arith.mult_clauses(), @words.word_add_0(), @lists.replicate()]),
    ]),
    hyps=[z, length],
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
        tm(m),
      ]),
      thm("sl_if"),
    ),
  )
  let if_rule = discharge(if_rule, ant => under(
    [length, bound],
    ant,
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        seq([@tactics.disch_tac, @tactics.accept_tac(nonzero)]),
        seq([@tactics.disch_tac, @tactics.accept_tac(zero)]),
      ]),
    ),
  ))
  let get = inst("st_local_get", [vs0, "[\{i(p0)}, \{i(m)}]", array(ys), "1"])
  let all = glue(with_labels(get, tm("(NIL : List[\{sassn}])")), if_rule, rule="sl_seq_l")
  let all = @drule.match_mp(thm("sl_triple_of_l"))(all)
  let all = under(
    [],
    @bool.mk_imp(@bool.mk_conj(length, bound), @kernel.concl(all)),
    seq([@tactics.disch_then(th => @tactics.strip_assume_tac(th)), @tactics.accept_tac(all)]),
  )
  record("example_fill", @bool.gen_all(all), kind="example")
}
