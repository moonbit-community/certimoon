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
    "fill_entry", "fill_step", "fill_exit", "example_fill",
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
    content="∀ m : (Limit_t, List[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]), ∀ n : Num, ∀ off : Num, ∀ bs : List[Word[Tybit0[Tybit0[Tybit0[Unit]]]]], ∀ r : ((Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, star(pts(n + off, bs), r, heap_of(m)) && !(bs == NIL) → load(m, n, off, LENGTH(bs)) == SOME(bs)",
  )
}

///|
test "sl_store_i32 states the store rule" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("sl_store_i32"))),
    content=(
      #|∀ p : (List[Value], List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, ∀ k : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ a : Num, ∀ off : Num, ∀ v : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ bs : List[Word[Tybit0[Tybit0[Tybit0[Unit]]]]], LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k)), V_num(ConstInt32(v))]) && star(pts(val(k) + off, bs), p(vs0, ls, gs), h), [Store(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ vs0 : List[Value], vs == vs0 && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls, gs), h))

    ),
  )
}

///|
test "example_store_load states the program's result" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("example_store_load"))),
    content=(
      #|∀ bs : List[Word[Tybit0[Tybit0[Tybit0[Unit]]]]], ∀ a : Num, ∀ k : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ off : Num, ∀ v : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ p : (List[Value], List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => star(pts(val(k) + off, bs), p(vs, ls, gs), h), [EConstNum(ConstInt32(k)), EConstNum(ConstInt32(v)), Store(T_i32, NONE, a, off), EConstNum(ConstInt32(k)), Load(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(v))]) && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls, gs), h))

    ),
  )
}

///|
test "sl_loop states the loop rule" {
  @logic.load()
  inspect(
    @term_syntax.print_term(@kernel.concl(@logic.thm("sl_loop"))),
    content=(
      #|∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ linv : (List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, ∀ qb : (List[Value], List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, ∀ ls : List[(List[Value], List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool], ∀ vs0 : List[Value], sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => vs == NIL && linv(lc, gs, h), bs, qb, CONS((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => vs == NIL && linv(lc, gs, h), ls)) → sl_triple_l((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => vs == vs0 && linv(lc, gs, h), [Loop(Tbv(ot), bs)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ r : List[Value], vs == APPEND(vs0, r) && qb(r, lc, gs, h), ls)

    ),
  )
}
