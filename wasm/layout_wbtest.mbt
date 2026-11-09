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
