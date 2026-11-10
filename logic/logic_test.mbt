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
