///|
test "the logic's lemmas are theorems, with no new axioms" {
  @logic.load()
  @testkit.check_axioms()
  for name in [
    "star_comm", "star_assoc", "star_mono", "read_pts", "heap_of_write", "write_pts",
    "load_pts", "store_pts",
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
