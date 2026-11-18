///|
test "atomic notation renders literals in match branches" {
  ignore(@arith.mult_clauses())
  @kernel.new_constant("render_match_literal", @kernel.bool_ty)
  let literal = @kernel.mk_const("render_match_literal", List([]))
  let atom = Atom::new(literal, text="32x")
  let t = @term_syntax.parse_term(
    "∀ n : Num, match n { 0 => true; other => render_match_literal }",
  )
  let (vars, body) = @basics.strip_forall(t)
  let scope = vars.to_array().map(@kernel.dest_var)
  let marks = notation_marks(t, [], [atom])
  let rendered = unmark(decorate(body, scope, marks).text, marks).0
  inspect(
    rendered,
    content=(
      #|match n { 0 => true; other => 32x }
    ),
  )
  assert_true(rendered.contains("32x"))
  let shown = statement(t, atoms=[atom])
  assert_true(shown.text.contains("32x"))
  assert_eq(shown.canonical, layout_statement(t))
}
