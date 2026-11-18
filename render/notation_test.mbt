///|
fn binary(name : String, extra~ : Bool = false) -> @kernel.Term raise {
  ignore(@bool.truth())
  let b = @kernel.bool_ty
  let arrow = (a, b) => @kernel.mk_type("fun", List([a, b]))
  if !@kernel.constants().iter().any(c => c.0 == name) {
    let result = if extra { arrow(b, b) } else { b }
    @kernel.new_constant(name, arrow(b, arrow(b, result)))
  }
  @kernel.mk_const(name, List([]))
}

///|
fn rule(
  name : String,
  symbol~ : String = "*",
  precedence~ : Int32 = 60,
  associativity~ : @render.Associativity = Right,
) -> @render.Infix raise {
  @render.Infix::new(binary(name), symbol~, precedence~, associativity~)
}

///|
fn formula(body : String) -> @kernel.Term raise {
  @term_syntax.parse_term("∀ p : Bool, ∀ q : Bool, ∀ r : Bool, " + body)
}

///|
test "infix rules are scoped and preserve grouping" {
  let infix = rule("render_join")
  let right = formula("render_join(p, render_join(q, r))")
  let original = @render.layout_statement(right)
  let shown = @render.statement(right, infixes=[infix])
  inspect(shown.text, content="∀ (p q r : Bool), p * q * r")
  assert_eq(shown.canonical, original)
  assert_eq(@render.layout_statement(right), original)
  assert_eq(shown.references.length(), 2)
  assert_true(shown.references.iter().all(r => r.constant == "render_join"))
  inspect(
    @render.layout_statement(formula("render_join(render_join(p, q), r)"), infixes=[
      infix,
    ]),
    content="∀ (p q r : Bool), (p * q) * r",
  )
  let left = rule("render_join", associativity=Left)
  inspect(
    @render.layout_statement(right, infixes=[left]),
    content="∀ (p q r : Bool), p * (q * r)",
  )
  let neither = rule("render_join", associativity=NonAssociative)
  inspect(
    @render.layout_statement(right, infixes=[neither]),
    content="∀ (p q r : Bool), p * (q * r)",
  )
}

///|
test "precedence and notation references" {
  let low = rule("render_low", symbol="<+>", precedence=40)
  let high = rule("render_high", symbol="<*>", precedence=60)
  inspect(
    @render.layout_statement(formula("render_high(render_low(p, q), r)"), infixes=[
      low, high,
    ]),
    content="∀ (p q r : Bool), (p <+> q) <*> r",
  )
  inspect(
    @render.layout_statement(formula("render_low(p, render_high(q, r))"), infixes=[
      low, high,
    ]),
    content="∀ (p q r : Bool), p <+> q <*> r",
  )
  let shown = @render.statement(
    formula("render_low(p, q) == render_high(q, r)"),
    infixes=[low, high],
  )
  let cs = shown.text.to_array()
  for reference in shown.references {
    let symbol = String::from_array(
      cs[reference.start:reference.start + reference.length].to_owned(),
    )
    assert_true(symbol == "<+>" || symbol == "<*>")
  }
}

///|
test "extra arguments, partial applications, and binders" {
  let c = binary("render_heap_star", extra=true)
  let infix = @render.Infix::new(
    c,
    symbol="*",
    precedence=60,
    associativity=Right,
  )
  inspect(
    @render.layout_statement(formula("render_heap_star(p, q, r)"), infixes=[
      infix,
    ]),
    content="∀ (p q r : Bool), (p * q)(r)",
  )
  let partial = formula("render_heap_star(p) == render_heap_star(q)")
  assert_eq(
    @render.layout_statement(partial, infixes=[infix]),
    @render.layout_statement(partial),
  )
  let nested = formula("((x : Bool) => render_heap_star(x, p, q))(r)")
  let shown = @render.statement(nested, infixes=[infix])
  assert_true(shown.text.contains("(x * p)(q)"), msg=shown.text)
  let shadow = @term_syntax.parse_term(
    "∀ render_heap_star : (Bool, Bool, Bool) -> Bool, render_heap_star(true, false, true)",
  )
  assert_eq(
    @render.layout_statement(shadow, infixes=[infix]),
    @render.layout_statement(shadow),
  )
}

///|
test "long infix chains wrap and keep their references" {
  let infix = rule("render_join")
  let mut body = "r"
  for _ in 0..<20 {
    body = "render_join(p, " + body + ")"
  }
  let shown = @render.statement(formula(body), infixes=[infix])
  assert_eq(shown.references.length(), 20)
  assert_true(shown.text.contains("\n"), msg=shown.text)
  assert_true(shown.text.split("\n").all(line => line.length() <= 80))
  let cs = shown.text.to_array()
  for reference in shown.references {
    assert_eq(cs[reference.start], '*')
  }
}

///|
test "infix configuration rejects variables and malformed operators" {
  let variable = @kernel.mk_var(
    "render_join",
    @kernel.type_of(binary("render_join")),
  )
  try @render.Infix::new(variable, symbol="*", precedence=60) catch {
    _ => ()
  } noraise {
    _ => fail("accepted a variable as an infix constant")
  }
  try rule("render_join", symbol="bad symbol") catch {
    _ => ()
  } noraise {
    _ => fail("accepted whitespace in an infix symbol")
  }
}

///|
test "numeric multiplication and separation notation have distinct references" {
  ignore(@arith.mult_clauses())
  let infix = rule("render_join")
  let t = @term_syntax.parse_term("render_join(2 * 3 == 6, true)")
  let shown = @render.statement(t, infixes=[infix])
  inspect(shown.text, content="(2 * 3 == 6) * true")
  assert_eq(shown.references.length(), 1)
  assert_eq(shown.references[0].start, 13)
  assert_true(
    @term_syntax.same_term(@term_syntax.parse_term(shown.canonical), t),
  )
}

///|
test "rules match the typed constant and Unicode offsets survive export" {
  let a = @kernel.aty
  let arrow = (a, b) => @kernel.mk_type("fun", List([a, b]))
  @kernel.new_constant("render_poly", arrow(a, arrow(a, a)))
  let b = @kernel.bool_ty
  let boolean = @kernel.mk_const("render_poly", List([(b, a)]))
  let functions = @kernel.mk_const("render_poly", List([(arrow(b, b), a)]))
  let infix = @render.Infix::new(boolean, symbol="🜁", precedence=60)
  let t = formula("render_poly(p, q)")
  let shown = @render.statement(t, infixes=[infix])
  inspect(shown.text, content="∀ (p q r : Bool), p 🜁 q")
  assert_eq(shown.references[0].length, 1)
  assert_eq(shown.text.to_array()[shown.references[0].start], '🜁')
  let id = @term_syntax.parse_term("(x : Bool) => x")
  let other = @kernel.mk_comb(@kernel.mk_comb(functions, id), id)
  assert_eq(
    @render.layout_statement(other, infixes=[infix]),
    @render.layout_statement(other),
  )
  let entry = @render.export_entry(
    "theorem",
    "poly",
    shown.text,
    ["render_poly"],
    [],
    "algebra/example.mbt:12:1-2@algebra",
    references=shown.references,
    canonical=shown.canonical,
  )
  assert_true(
    entry is { "references": Array(refs), "canonical_statement": String(_), .. } &&
    refs.length() == 1,
  )
}

///|
test "dependency traversal accepts independent theories and cycles" {
  let definitions = [
    ("algebra", "a", ["a"], ["b"]),
    ("algebra", "b", ["b"], ["a", "="]),
    ("unused", "c", ["c"], []),
  ]
  let (dependencies, outside) = @render.depends_on(["a"], definitions)
  assert_eq(dependencies, [("algebra", "a"), ("algebra", "b")])
  assert_eq(outside, ["="])
}

///|
test "infix operands retain their expected type without redundant annotations" {
  let infix = rule("render_literal_join")
  @kernel.new_constant("render_literal", @kernel.aty)
  let literal = @kernel.mk_const(
    "render_literal",
    List([(@kernel.bool_ty, @kernel.aty)]),
  )
  let p = @kernel.mk_var("render_operand_0", @kernel.bool_ty)
  let body = @kernel.mk_comb(
    @kernel.mk_comb(binary("render_literal_join"), literal),
    p,
  )
  let t = @bool.mk_forall(p, body)
  let shown = @render.statement(t, infixes=[infix])
  inspect(
    shown.text,
    content="∀ (render_operand_0 : Bool), render_literal * render_operand_0",
  )
  assert_eq(shown.canonical, @render.layout_statement(t))
  assert_eq(shown.references.length(), 1)
}

///|
test "applications containing notation retain their expected result type" {
  let infix = rule("render_nested_join")
  let arrow = @kernel.mk_type("fun", List([@kernel.bool_ty, @kernel.aty]))
  @kernel.new_constant("render_convert", arrow)
  let convert = @kernel.mk_const(
    "render_convert",
    List([(@kernel.bool_ty, @kernel.aty)]),
  )
  let p = @kernel.mk_var("p", @kernel.bool_ty)
  let q = @kernel.mk_var("q", @kernel.bool_ty)
  let joined = @kernel.mk_comb(
    @kernel.mk_comb(binary("render_nested_join"), p),
    q,
  )
  let t = @bool.mk_forall(
    p,
    @bool.mk_forall(q, @kernel.mk_comb(convert, joined)),
  )
  let shown = @render.statement(t, infixes=[infix])
  inspect(shown.text, content="∀ (p q : Bool), render_convert((p * q))")
  assert_eq(shown.canonical, @render.layout_statement(t))
  assert_eq(shown.references.length(), 1)
}
