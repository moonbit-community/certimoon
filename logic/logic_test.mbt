///|
test "the logic's lemmas are theorems, with no new axioms" {
  @logic.load()
  @testkit.check_axioms()
  for name in [
    "star_comm", "star_assoc", "star_mono", "read_pts", "heap_of_write", "write_pts",
    "load_pts", "store_pts", "safe_mono", "triple_conseq", "sl_conseq", "sl_frame",
    "sl_const", "arity_binop", "prefix_binop", "sl_binop", "arity_load", "prefix_load",
    "sl_load_i32", "arity_store", "prefix_store", "sl_store_i32",
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
      #|∀ p : (List[Value], List[Value], (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) -> Bool, ∀ k : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ a : Num, ∀ off : Num, ∀ v : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]], ∀ bs : List[Word[Tybit0[Tybit0[Tybit0[Unit]]]]], LENGTH(bs) == 4 → sl_triple((vs : List[Value]) => (ls : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k)), V_num(ConstInt32(v))]) && star(pts(val(k) + off, bs), p(vs0, ls), h), [Store(T_i32, NONE, a, off)], (vs : List[Value]) => (ls : List[Value]) => (h : (Num) -> Option[Word[Tybit0[Tybit0[Tybit0[Unit]]]]]) => ∃ vs0 : List[Value], vs == vs0 && star(pts(val(k) + off, serialise_i32(v)), p(vs0, ls), h))
    ),
  )
}
