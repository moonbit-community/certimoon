///|
test "direct definition eligibility excludes general definition cases" {
  load()
  for
    equation in [
      "direct_f((x : Num)) == x + 1", "∀ y : A, ∀ x : A, direct_pair(x, y) == (x, y)",
      "direct_id == ((x : A) => x)", "direct_const == (0 : Num)",
    ] {
    assert_true(is_direct_definition(tm(equation)), msg=equation)
  }
  for
    equation in [
      "general_rec((x : Num)) == general_rec(x)", "general_pattern(0) == (0 : Num)",
      "general_repeat((x : Num), x) == x", "general_hidden((x : Num)) == (y : Num)",
      "general_type == (∀ x : A, x == x)", "∀ f : (Num) -> Num, f(x) == x", "∀ unused : Num, general_unused((x : Num)) == x",
      "(general_clauses(0) == 0) && (general_clauses(1) == 1)", "T",
    ] {
    assert_false(is_direct_definition(tm(equation)), msg=equation)
  }
}

///|
test "direct definition theorem shape matches the general processor" {
  load()
  for
    (fast, slow, equation) in [
      ("fast_shape_const", "slow_shape_const", " == (0 : Num)"),
      ("fast_shape_free", "slow_shape_free", "((x : Num), (y : Num)) == x + y"),
      ("fast_shape_poly", "slow_shape_poly", " == ((x : A) => x)"),
      ("fast_shape_quant", "slow_shape_quant", "((x : A), (y : A)) == (x, y)"),
      (
        "fast_shape_partial", "slow_shape_partial", "((x : Num), (y : Num)) == x + y",
      ),
    ] {
    let prefix = if fast == "fast_shape_quant" {
      "∀ y : A, ∀ x : A, "
    } else if fast == "fast_shape_partial" {
      "∀ y : Num, "
    } else {
      ""
    }
    let goal = tm(prefix + fast + equation)
    assert_true(is_direct_definition(goal), msg=fast)
    let actual = define_equation(goal)
    let expected = @define.define_(tm(prefix + slow + equation))
    let (_, fast_body) = @basics.strip_forall(@kernel.concl(actual))
    let (_, slow_body) = @basics.strip_forall(@kernel.concl(expected))
    let fast_head = @basics.strip_comb(@kernel.dest_eq(fast_body).0).0
    let slow_head = @basics.strip_comb(@kernel.dest_eq(slow_body).0).0
    let renamed = @basics.subst(
      @list.List([(fast_head, slow_head)]),
      @kernel.concl(expected),
    )
    assert_true(@basics.aconv(@kernel.concl(actual), renamed), msg=fast)
    assert_true(@kernel.hyp(actual).is_empty(), msg=fast)
    assert_true(@kernel.hyp(expected).is_empty(), msg=slow)
  }
  @testkit.check_axioms()
}

///|
test "direct definitions remain registered for benign redefinition" {
  load()
  let before = @pair.the_definitions().val.length()
  let first = define_equation(tm("direct_redefinition((x : Num)) == x + 1"))
  assert_eq(@pair.the_definitions().val.length(), before + 1)
  let goal = tm("direct_redefinition((x : Num)) == x + 1")
  assert_false(is_direct_definition(goal))
  let again = define_equation(goal)
  let general = @define.define_(goal)
  assert_true(@basics.aconv(@kernel.concl(first), @kernel.concl(again)))
  assert_true(@basics.aconv(@kernel.concl(first), @kernel.concl(general)))
  assert_eq(@pair.the_definitions().val.length(), before + 1)
  @testkit.check_axioms()
}

///|
test "recursive pattern definitions retain the general processor" {
  load()
  let goal = tm(
    "(fallback_length(([] : List[Num])) == 0) && " +
    "(fallback_length(CONS(h, t)) == fallback_length(t) + 1)",
  )
  assert_false(is_direct_definition(goal))
  let th = define_equation(goal)
  assert_true(@kernel.hyp(th).is_empty())
  let result = prove(
    tm("fallback_length([4, 5]) == 2"),
    seq([
      @simp.rewrite_tac(@list.List([th])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  assert_true(@kernel.hyp(result).is_empty())
  @testkit.check_axioms()
}
