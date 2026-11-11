///|
test "a statement with hypotheses is laid out, and reads back" {
  load()
  let t = @term_syntax.parse_term(
    "∀ x : Num, ∀ y : Num, x < y && y < 5 → (∀ z : Num, z == x → (∃ w : Num, w < 5 && z == w) || x == 0)",
  )
  inspect(
    layout_statement(t),
    content=(
      #|∀ (x y z : Num)
      #|if
      #|  1. x < y
      #|  2. y < 5
      #|  3. z == x
      #|then
      #|  ∃ (w : Num),
      #|    w < 5
      #|    && z == w
      #|or
      #|  x == 0
    ),
  )
}

///|
test "a name bound twice is not shown at the top" {
  load()
  // the inner x is another variable: the layout keeps it where it is
  let t = @term_syntax.parse_term(
    "∀ x : Num, x < 5 → (∀ x : Num, x == x)",
  )
  inspect(
    layout_statement(t),
    content=(
      #|∀ (x : Num)
      #|if
      #|  1. x < 5
      #|then
      #|  ∀ x : Num, x == x
    ),
  )
}

///|
test "a statement with no hypotheses" {
  load()
  inspect(
    layout_statement(@term_syntax.parse_term("∀ x : Num, ∀ y : Num, x + y == y + x")),
    content="∀ (x y : Num), x + y == y + x",
  )
  inspect(layout_statement(@term_syntax.parse_term("1 < 2")), content="1 < 2")
}

///|
test "a definition's equations, a line each" {
  load()
  inspect(
    layout_statement(@term_syntax.parse_term("1 < 2 && 2 < 3 && (∀ x : Num, x == x)")),
    content=(
      #|1 < 2
      #|&& 2 < 3
      #|&& ∀ x : Num, x == x
    ),
  )
}

///|
test "a long line is broken by its structure, and only its whitespace changes" {
  let concl = "  sl_triple_m(fs, inst, (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : Heap) => vs == APPEND(vs0, [V_num(ConstInt32(p)), V_num(ConstInt32(word(0))), V_num(ConstInt32(n))]) && lc == lc0 && star(arr(val(p), xs), fp(gs, ms), h), [Call(0)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : Heap) => ∃ ys : List[W32], vs == vs0 && lc == lc0 && sorted(ys) && perm(ys, xs) && LENGTH(ys) == LENGTH(xs) && star(arr(val(p), ys), fp(gs, ms), h), NIL)"
  inspect(
    break_line(concl),
    content=(
      #|  sl_triple_m(
      #|    fs,
      #|    inst,
      #|    (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) =>
      #|    (ms : Num) => (h : Heap) =>
      #|      vs == APPEND(
      #|        vs0,
      #|        [V_num(ConstInt32(p)), V_num(ConstInt32(word(0))),
      #|         V_num(ConstInt32(n))])
      #|      && lc == lc0
      #|      && star(arr(val(p), xs), fp(gs, ms), h),
      #|    [Call(0)],
      #|    (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) =>
      #|    (ms : Num) => (h : Heap) =>
      #|      ∃ ys : List[W32],
      #|        vs == vs0
      #|        && lc == lc0
      #|        && sorted(ys)
      #|        && perm(ys, xs)
      #|        && LENGTH(ys) == LENGTH(xs)
      #|        && star(arr(val(p), ys), fp(gs, ms), h),
      #|    NIL)
    ),
  )
  let hyp = "  2. EL(sfunc_ind(inst, 1), fs) == Func_native(inst, Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], partition_code)"
  inspect(
    break_line(hyp),
    content=(
      #|  2. EL(sfunc_ind(inst, 1), fs) == Func_native(
      #|       inst,
      #|       Tf([T_num(T_i32), T_num(T_i32), T_num(T_i32)], [T_num(T_i32)]),
      #|       [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)],
      #|       partition_code)
    ),
  )
  // a short line stays as it is, and so does one with a string in it
  inspect(break_line("  f(x, y)"), content="  f(x, y)")
  let s = "  f(\"" + "a, ".repeat(40) + "\")"
  inspect(break_line(s) == s, content="true")
}
