///|
test "the logic's lemmas are theorems, with no new axioms" {
  @logic.load()
  @testkit.check_axioms()
  for name in [
    "star_comm", "star_assoc", "star_mono", "read_pts", "heap_of_write", "write_pts",
    "load_pts", "store_pts", "safe_mono", "triple_conseq", "sl_conseq", "sl_frame",
    "sl_const", "arity_binop", "prefix_binop", "sl_binop", "arity_load", "prefix_load",
    "sl_load_i32", "arity_store", "prefix_store", "sl_store_i32", "safe_seq", "triple_seq",
    "sl_seq", "deserialise_serialise_i32", "example_store_load", "safe_safel",
    "sl_triple_l_of", "safel_seq", "sl_seq_l", "safel_mono", "triple_l_conseq", "sl_conseq_l",
    "sl_frame_l", "sl_br", "label_steps", "br_unique", "br_stuck",
    "label_safe", "block_step", "sl_block", "safel_down", "loop_step", "sl_loop",
    "gvals_mems_update", "el_list_update_other", "el_gvals", "globs_ok_set", "s_mems_set",
    "gvals_set", "sl_global_get", "sl_global_set", "split_at", "el_split", "list_update_split",
    "local_get_step", "local_get_cases", "local_set_step", "local_set_cases", "sl_local_get",
    "sl_local_set", "sl_local_tee", "prefix_br_if", "sl_br_if", "prefix_if", "sl_if",
    "pts_split", "lift_ex", "lift_pure", "sl_ex_l", "sl_pure_l", "sl_nil_l", "safel_nil",
    "sl_triple_of_l", "st_snoc_ex", "st_const", "st_binop", "st_local_get", "st_local_set",
    "sum_to_step", "sum_inv_step", "example_sum", "arr_split", "arr_cons", "arr_focus",
    "star_left_comm", "star_pure_r", "st_arr_store", "st_arr_load", "replicate_shift",
    "fill_entry", "fill_step", "fill_exit", "example_fill", "sl_testop", "sl_relop",
    "st_testop", "st_relop", "wsum_snoc", "wasm_bool_zero", "asum_addr", "asum_step",
    "asum_exit", "example_array_sum", "sl_unop", "sl_convert", "sl_reinterpret", "sl_nop", "is_val_v_to_e", "drop_cases", "sl_drop", "select_cases", "sl_select", "sl_load_i64",
    "sl_store_i64", "sl_load_packed_i32", "sl_load_packed_i64", "sl_store_packed_i32", "sl_store_packed_i64", "serialise_i64_length", "store_length", "mem_length_append", "heap_of_append",
    "star_grow", "sl_memory_size", "sl_memory_grow", "sl_pre_l", "sl_step_l", "sl_nil_st",
    "sl_br_st", "sl_br_if_st", "sl_if_st", "sl_block_st", "sl_loop_st", "sl_cons_l", "addr_at",
    "st_arr_load_at", "st_arr_store_at", "perm_refl", "perm_swap", "sorted_insert",
    "sorted_snoc_le", "snoc_cases", "list_update_snoc", "isort_bound", "isort_inner_entry",
    "isort_empty", "isort_stop", "isort_shift", "isort_next", "isort_done", "isort_start",
    "isort_none", "example_insertion_sort", "has_call_b_eq", "has_call_eq", "call_free_vals",
    "call_free_basic", "call_free_lfill", "no_call_v_to_e", "s_funcs_updates", "simple_call_free",
    "call_free_step", "safel_keep", "sl_triple_m_of", "sl_seq_m", "sl_conseq_m", "safe_step", "safe_run", "safe_progress", "safe_adequate",
    "sl_triple_adequate", "sl_triple_m_adequate", "hunion_emp", "star_emp_r", "lift_emp",
    "sl_triple_m_adequate_whole", "no_trap_frame",
    "frame_simple", "frame_base", "frame_steps", "ret_not_vals", "return_stuck", "br_ret_distinct",
    "frame_can_step", "frame_next", "frame_safe", "call_step", "invoke_base", "invoke_step",
    "call_safe", "label_safe_top", "sl_call", "double_body", "example_call", "safer_vals",
    "safel_safer", "safer_safel", "safer_mono", "safer_down", "safer_trap", "safer_det_step",
    "safer_seq", "ret_unique", "ret_frame_case", "safer_label", "safer_label_top",
    "frame_can_step_r", "frame_next_r", "frame_safe_r", "specs_down", "sl_triple_g_of_m",
    "sl_triple_g_of", "sl_triple_m_of_g", "sl_seq_g", "sl_conseq_g", "sl_conseq_ret_g",
    "sl_nil_g", "sl_false_g", "sl_ex_g", "sl_pure_g", "sl_br_g", "sl_return_g", "keep_in_mod",
    "sl_br_if_g", "sl_if_g", "sl_block_g", "sl_loop_g", "sl_call_g", "sl_funs_g", "sl_step_g",
    "sl_pre_g", "sl_cons_g", "sl_nil_st_g", "sl_br_st_g", "sl_br_if_st_g", "sl_if_st_g",
    "sl_block_st_g", "sl_loop_st_g", "sl_call_st_g", "sl_return_st_g", "fact_w_suc",
    "fact_w_step", "fact_call", "fact_body", "fact_specs", "example_fact", "fact_closed", "sl_call_spec_g",
    "val_add_small", "val_sub_one", "val_add_one", "nonempty_cons", "el_at", "update_at", "el_mid", "el_mid2", "part_swap",
    "count_rot", "length_rot", "all_rot", "perm_move", "perm_rot", "partition_body", "qs_call",
    "partition_call", "qs_split", "sorted_short", "mem_count", "perm_all", "sorted_join", "perm_join",
    "butlast_cons", "quicksort_body", "partition_fn", "quicksort_specs", "example_quicksort",
    "s_tabs_updates", "call_indirect_step", "call_indirect_can_step", "sl_call_indirect_g",
    "sl_call_indirect_st_g", "double_spec_holds", "double_body_g", "double_specs", "apply_body",
    "example_indirect", "apply_closed",
  ] {
    assert_true(@kernel.hyp(@logic.thm(name)).is_empty(), msg=name)
  }
}

///|
test "load_pts states the load rule" {
  @logic.load()
  let show = (name : String) => @term_syntax.print_term(@kernel.concl(@logic.thm(name)))
  inspect(
    show("load_pts"),
    content=(
      #|∀ m : (Limit_t, List[Word[8]]), ∀ n : Num, ∀ off : Num, ∀ bs : List[Word[8]], ∀ r : ((Num) -> Option[Word[8]]) -> Bool, star(pts(n + off, bs), r, heap_of(m)) && !(bs == NIL) → load(m, n, off, LENGTH(bs)) == SOME(bs)
    ),
  )
}

///|
test "sl_store_i32 states the store rule" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("sl_store_i32"))),
    content=(
      #|∀ p : (List[Value], List[Value], List[Value], Num, (Num) -> Option[Word[8]]) -> Bool, ∀ k : Word[32], ∀ a : Num, ∀ off : Num, ∀ v : Word[32], ∀ bs : List[Word[8]], LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k)), V_num(ConstInt32(v))]) && star(pts(val(k) + off, bs), p(vs0, ls, gs, ms), h), [Store(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => ∃ vs0 : List[Value], vs == vs0 && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls, gs, ms), h))



    ),
  )
}

///|
test "example_store_load states the program's result" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("example_store_load"))),
    content=(
      #|∀ bs : List[Word[8]], ∀ a : Num, ∀ k : Word[32], ∀ off : Num, ∀ v : Word[32], ∀ p : (List[Value], List[Value], List[Value], Num, (Num) -> Option[Word[8]]) -> Bool, LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => star(pts(val(k) + off, bs), p(vs, ls, gs, ms), h), [EConstNum(ConstInt32(k)), EConstNum(ConstInt32(v)), Store(T_i32, NONE, a, off), EConstNum(ConstInt32(k)), Load(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(v))]) && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls, gs, ms), h))



    ),
  )
}

///|
test "sl_loop states the loop rule" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("sl_loop"))),
    content=(
      #|∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ linv : (List[Value], List[Value], Num, (Num) -> Option[Word[8]]) -> Bool, ∀ qb : (List[Value], List[Value], List[Value], Num, (Num) -> Option[Word[8]]) -> Bool, ∀ ls : List[(List[Value], List[Value], List[Value], Num, (Num) -> Option[Word[8]]) -> Bool], ∀ vs0 : List[Value], sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => vs == NIL && linv(lc, gs, ms, h), bs, qb, CONS((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => vs == NIL && linv(lc, gs, ms, h), ls)) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => vs == vs0 && linv(lc, gs, ms, h), [Loop(Tbv(ot), bs)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : (Num) -> Option[Word[8]]) => ∃ r : List[Value], vs == APPEND(vs0, r) && qb(r, lc, gs, ms, h), ls)



    ),
  )
}

///|
/// The logic's theory as a document: __snapshot__/theory.md. It is in this
/// file so that a test run loads the logic once (each test file is its own
/// process).
test "the theory listing" (t : @test.Test) {
  t.write(@logic.listing())
  t.snapshot(filename="theory.md")
}

///|
/// The same as data, for the review site (tools/review_site.py):
/// __snapshot__/theory.json.
test "the theory as data" (t : @test.Test) {
  t.write(@logic.listing_json())
  t.snapshot(filename="theory.json")
}

///|
/// What each theorem depends on: __snapshot__/dependencies.md.
test "what each theorem depends on" (t : @test.Test) {
  t.write(@logic.dependencies())
  t.snapshot(filename="dependencies.md")
}

///|
test "a program proved through the public API" {
  @logic.load()
  let w = @logic.w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  // local 0 becomes the larger (unsigned) of locals 0 and 1:
  //   local.get 0; local.get 1; i32.lt_u; if; local.get 1; local.set 0; end
  let code = "[Local_get(0), Local_get(1), Relop(T_i32, Relop_i(Lt(U))), If(Tbv(NONE), [Local_get(1), Local_set(0)], NIL)]"
  let th = @logic.sym_prove(
    "api_max",
    "∀ vs0 : List[Value], ∀ x : \{w}, ∀ y : \{w}, ∀ R : \{@logic.rty}, sl_triple(st(vs0, [\{i("x")}, \{i("y")}], R), \{code}, st(vs0, [\{i("if word_ult(x, y) { y } else { x }")}, \{i("y")}], R))",
    [],
    [],
  )
  assert_true(@kernel.hyp(th).is_empty())
  assert_true(@kernel.hyp(@logic.thm("api_max")).is_empty())
  // a user's theorem is not in the package's theory listing
  assert_false(@logic.listing().contains("api_max"))
}

// Non-vacuity checks for the closed theorems. A theorem `if H1 ... Hn
// then C` holds trivially when nothing satisfies its hypotheses together,
// and the kernel would not notice. For each closed theorem, a test picks a
// concrete store, frame and arguments, proves every hypothesis about them
// in the kernel (by computation, and the run by the evaluator, which
// proves each step from the reduction rules), and so derives the
// conclusion for them. It then proves the conclusion's first alternative
// (the run ended normally, as the theorem describes) for the result the
// run gave.

///|
/// The definitions the computations here use, besides the port's.
fn closed_defs() -> Array[@kernel.Thm] raise {
  [
    @logic.thm("globs_ok"),
    @logic.thm("gvals"),
    @logic.thm("words_bytes"),
    @logic.thm("sorted"),
    @logic.thm("fact_w"),
    @pair.snd(),
    @lists.pairwise(),
    @lists.all(),
    // i < 0 is false (for globs_ok with no globals)
    @bool.conjunct1(@arith.lt()),
  ] +
  @logic.program_defs()
}

///|
/// `t`, proved by computing it to true with `conv`.
fn computed(conv : @equal.Conv, t : @kernel.Term) -> @kernel.Thm raise {
  let th = conv(t)
  @bool.eqt_elim(th) catch {
    _ =>
      raise Failure(
        "not true by computation: " +
        @logic.show(t) +
        "\ncomputes to: " +
        @logic.show(@equal.rhs(@kernel.concl(th))),
      )
  }
}

///|
/// The parts of `t` along its right-nested `&&`.
fn right_conjuncts(t : @kernel.Term) -> Array[@kernel.Term] raise {
  let parts = []
  let mut t = t
  while @basics.is_conj(t) {
    let (a, b) = @basics.dest_conj(t)
    parts.push(a)
    t = b
  }
  parts.push(t)
  parts
}

///|
/// The conjunction of `ths`' statements, nested to the right.
fn conj_all(ths : Array[@kernel.Thm]) -> @kernel.Thm raise {
  let mut acc = ths[ths.length() - 1]
  for i = ths.length() - 2; i >= 0; i = i - 1 {
    acc = @bool.conj(ths[i], acc)
  }
  acc
}

///|
/// `th`, a statement `∀ xs, ...`, for the values `vals` of its variables
/// by name (a variable with no value stays).
fn instantiate(
  th : @kernel.Thm,
  vals : Map[String, @kernel.Term],
) -> @kernel.Thm raise {
  let (vars, _) = @basics.strip_forall(@kernel.concl(th))
  let args = vars
    .to_array()
    .map(fn(v) raise {
      match vals.get(@kernel.dest_var(v).0) {
        Some(t) => t
        None => v
      }
    })
  @bool.specl(@list.List(args), th)
}

///|
/// The closed theorem `name` for the values `vals`: each hypothesis but the
/// last proved by computing with `conv`, and the last, the run
/// `reduce_trans(cfg, (s2, f2, es2))`, by the evaluator, which also gives
/// the final configuration s2, f2, es2. The conclusion for these values,
/// and the final configuration.
fn run_closed(
  name : String,
  vals : Map[String, @kernel.Term],
  conv : @equal.Conv,
) -> (@kernel.Thm, @kernel.Term) raise {
  let closed = @logic.thm(name)
  // the run, from the configuration in the last hypothesis
  let (ante, _) = @basics.dest_imp(@kernel.concl(instantiate(closed, vals)))
  let hyps = right_conjuncts(ante)
  let cfg = @kernel.rand(@kernel.rator(hyps[hyps.length() - 1]))
  // the program written out (a run from MAP(Basic, apply_code)), then
  // the run restated for cfg
  let cfg_eq = conv(cfg) catch { _ => @kernel.refl(cfg) }
  let run = @wasm.run(@equal.rhs(@kernel.concl(cfg_eq)))
  let fin = @kernel.rand(@kernel.concl(run))
  let rt = @kernel.rator(@kernel.rator(@kernel.concl(run)))
  let run = @kernel.eq_mp(
    @equal.sym(@equal.ap_thm(@equal.ap_term(rt, cfg_eq), fin)),
    run,
  )
  let (s2, rest) = @pair.dest_pair(fin)
  let (f2, es2) = @pair.dest_pair(rest)
  vals["s2"] = s2
  vals["f2"] = f2
  vals["es2"] = es2
  let th = instantiate(closed, vals)
  let (ante, _) = @basics.dest_imp(@kernel.concl(th))
  let hyps = right_conjuncts(ante)
  let proved = hyps.mapi(fn(i, h) raise {
    if i == hyps.length() - 1 {
      run
    } else {
      computed(conv, h)
    }
  })
  (@bool.mp(th, conj_all(proved)), fin)
}

///|
/// The first alternative of `concl`'s statement `A || B`, proved: A's
/// conjuncts by `given` (by statement) or by computing with `conv`, with
/// `witness` for its `∃` if it has one.
fn first_alternative(
  concl : @kernel.Thm,
  witness : @kernel.Term?,
  given : Array[@kernel.Thm],
  conv : @equal.Conv,
) -> @kernel.Thm raise {
  let (a, _) = @basics.dest_disj(@kernel.concl(concl))
  let prove_body = fn(body : @kernel.Term) raise {
    let parts = right_conjuncts(body).map(fn(c) raise {
      match given.search_by(g => @basics.aconv(@kernel.concl(g), c)) {
        Some(k) => given[k]
        None => computed(conv, c)
      }
    })
    conj_all(parts)
  }
  match witness {
    Some(w) => {
      let (v, body) = @basics.dest_exists(a)
      let b = @kernel.vsubst(@list.List([(w, v)]), body)
      @bool.exists_rule(a, w, prove_body(b))
    }
    None => prove_body(a)
  }
}

///|
/// `perm(ys, xs)` for written-out lists, `ys` a reordering of `xs`: from
/// `perm_refl` by `perm_swap`s, moving each element of ys into its place.
fn perm_by_swaps(
  ys : Array[@kernel.Term],
  xs : Array[@kernel.Term],
) -> @kernel.Thm raise {
  let ty = @kernel.type_of(xs[0])
  let list = (items : Array[@kernel.Term]) => @lists.mk_list(@list.List(items), ty)
  let append = @simp.pure_rewrite_conv(@list.List([@lists.append()]))
  let cur = xs.copy()
  let mut th = @bool.spec(list(xs), @logic.thm("perm_refl"))
  for i in 0..<ys.length() {
    let mut k = i
    while !@basics.aconv(cur[k], ys[i]) {
      k = k + 1
    }
    // swap ys[i] down from k to i
    for m = k - 1; m >= i; m = m - 1 {
      let vals : Map[String, @kernel.Term] = {
        "A": list(cur[:m].to_owned()),
        "e": cur[m],
        "x": cur[m + 1],
        "ts": list(cur[m + 2:].to_owned()),
        "ys": list(xs),
      }
      let swap = @equal.conv_rule(append, instantiate(@logic.thm("perm_swap"), vals))
      th = @bool.mp(swap, th)
      let e = cur[m]
      cur[m] = cur[m + 1]
      cur[m + 1] = e
    }
  }
  th
}

///|
test "fact_closed's hypotheses hold together: fact(5) runs to 120" {
  @logic.load()
  let conv = @wasm.compute_conv(closed_defs(), suc=[("fact_w", 1, 0)])
  let value = (t : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(t))))
  let inst = value("Inst([Tf([T_num(T_i32)], [T_num(T_i32)])], [0], NIL, [0], NIL, NIL, NIL)")
  let i = @logic.show(inst)
  // a store with fact_code as function 0, and a memory (empty)
  let s = value(
    "Wstore([Func_native(\{i}, Tf([T_num(T_i32)], [T_num(T_i32)]), NIL, fact_code)], NIL, [(Limit_t(0, NONE), NIL)], NIL, NIL, NIL)",
  )
  let vals : Map[String, @kernel.Term] = {
    "fs": value("s_funcs(\{@logic.show(s)})"),
    "inst": inst,
    "s": s,
    "f": value("Wframe(NIL, \{i})"),
    "j": @logic.tm("0"),
    "x": @logic.tm("(word(5) : Word[32])"),
    "vs0": @logic.tm("(NIL : List[Value])"),
  }
  let (concl, fin) = run_closed("fact_closed", vals, conv)
  inspect(@kernel.hyp(concl).is_empty(), content="true")
  inspect(
    @logic.show(@pair.dest_pair(@pair.dest_pair(fin).1).1),
    content="[Basic(EConstNum(ConstInt32(word(120))))]",
  )
  // the run ended normally, with fact_w(5) on the stack
  let alt = first_alternative(concl, None, [], conv)
  inspect(@kernel.hyp(alt).is_empty(), content="true")
}

///|
test "quicksort_closed's hypotheses hold together: [3, 1, 2] is sorted in place" {
  @logic.load()
  let conv = @wasm.compute_conv(closed_defs())
  let value = (t : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(t))))
  let inst = value(
    "Inst([Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], NIL), Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], [T_num(T_i32)])], [0, 1], NIL, [0], NIL, NIL, NIL)",
  )
  let i = @logic.show(inst)
  // the array [3, 1, 2] at address 4, between 4 bytes before and 2 after
  let before = "[(word(170) : Word[8]), word(187), word(204), word(221)]"
  let xs = "[(word(3) : Word[32]), word(1), word(2)]"
  let after = "[(word(238) : Word[8]), word(255)]"
  let s = value(
    "Wstore([Func_native(\{i}, Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], NIL), [T_num(T_i32)], quicksort_code), Func_native(\{i}, Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], partition_code)], NIL, [(Limit_t(0, NONE), APPEND(\{before}, APPEND(words_bytes(\{xs}), \{after})))], NIL, NIL, NIL)",
  )
  let vals : Map[String, @kernel.Term] = {
    "fs": value("s_funcs(\{@logic.show(s)})"),
    "inst": inst,
    "s": s,
    "f": value("Wframe(NIL, \{i})"),
    "j": @logic.tm("0"),
    "p": @logic.tm("(word(4) : Word[32])"),
    "n": @logic.tm("(word(3) : Word[32])"),
    "xs": @logic.tm(xs),
    "before": @logic.tm(before),
    "after": @logic.tm(after),
    "vs0": @logic.tm("(NIL : List[Value])"),
  }
  let (concl, fin) = run_closed("quicksort_closed", vals, conv)
  inspect(@kernel.hyp(concl).is_empty(), content="true")
  // the memory's bytes after the run: the array holds 1, 2, 3 (as
  // little-endian words), the bytes around it as they were
  let s2 = @logic.show(@pair.dest_pair(fin).0)
  inspect(
    @logic.show(value("MAP(val, SND(EL(0, s_mems(\{s2}))))")),
    content="[170, 187, 204, 221, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 238, 255]",
  )
  // the run ended normally, with [1, 2, 3] in the array's place
  let ys = @basics.dest_list(@logic.tm("[(word(1) : Word[32]), word(2), word(3)]")).to_array()
  let perm = perm_by_swaps(ys, @basics.dest_list(@logic.tm(xs)).to_array())
  let witness = @lists.mk_list(@list.List(ys), @kernel.type_of(ys[0]))
  let alt = first_alternative(concl, Some(witness), [perm], conv)
  inspect(@kernel.hyp(alt).is_empty(), content="true")
}

///|
test "apply_closed's hypotheses hold together: apply(21, 0) calls double, to 42" {
  @logic.load()
  let conv = @wasm.compute_conv(closed_defs())
  let value = (t : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(t))))
  let tf = "Tf([T_num(T_i32)], [T_num(T_i32)])"
  // the instance: type 0 is double's, function 0, table 0 and memory 0
  let inst = value("Inst([\{tf}], [0], [0], [0], NIL, NIL, NIL)")
  let i = @logic.show(inst)
  // a store with double_code as function 0, a table holding it at 0, and
  // a memory (empty)
  let s = value(
    "Wstore([Func_native(\{i}, \{tf}, NIL, double_code)], [(T_tab(Limit_t(1, NONE), T_func_ref), [ConstRefFunc(0)])], [(Limit_t(0, NONE), NIL)], NIL, NIL, NIL)",
  )
  let vals : Map[String, @kernel.Term] = {
    "fs": value("s_funcs(\{@logic.show(s)})"),
    "inst": inst,
    "a": @logic.tm("0"),
    "s": s,
    "f": value(
      "Wframe([V_num(ConstInt32(word(21))), V_num(ConstInt32(word(0)))], \{i})",
    ),
    "j": @logic.tm("0"),
    "x": @logic.tm("(word(21) : Word[32])"),
    "k": @logic.tm("(word(0) : Word[32])"),
  }
  let (concl, fin) = run_closed("apply_closed", vals, conv)
  inspect(@kernel.hyp(concl).is_empty(), content="true")
  inspect(
    @logic.show(@pair.dest_pair(@pair.dest_pair(fin).1).1),
    content="[Basic(EConstNum(ConstInt32(word(42))))]",
  )
  // the run ended normally, with x + x on the stack
  let alt = first_alternative(concl, None, [], conv)
  inspect(@kernel.hyp(alt).is_empty(), content="true")
}
