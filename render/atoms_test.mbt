///|
fn sample_atom(text~ : String = "32x") -> @render.Atom raise {
  ignore(binary("render_atom_build"))
  @render.Atom::new(
    @term_syntax.parse_term("render_atom_build(true, false)"),
    text~,
  )
}

///|
test "atomic rules replace complete terms and compose with infix rules" {
  let atom = sample_atom()
  let t = @term_syntax.parse_term(
    "∀ p : Bool, render_atom_build(true, false) == render_atom_build(p, false)",
  )
  let shown = @render.statement(t, atoms=[atom])
  inspect(
    shown.text,
    content="∀ (p : Bool), 32x == render_atom_build(p, false)",
  )
  assert_eq(shown.canonical, @render.layout_statement(t))
  assert_eq(shown.references.length(), 1)
  assert_eq(shown.references[0].constant, "render_atom_build")
  let infix = rule("render_atom_join")
  let mixed = @term_syntax.parse_term(
    "∀ p : Bool, render_atom_join(render_atom_build(true, false), render_atom_build(p, false))",
  )
  inspect(
    @render.layout_statement(mixed, infixes=[infix], atoms=[atom]),
    content="∀ (p : Bool), 32x * render_atom_build(p, false)",
  )
}

///|
test "atomic rules keep type instances and bound variables distinct" {
  ignore(@bool.truth())
  @kernel.new_constant("render_atom_poly", @kernel.aty)
  let boolean = @kernel.mk_const(
    "render_atom_poly",
    List([(@kernel.bool_ty, @kernel.aty)]),
  )
  let atom = @render.Atom::new(boolean, text="0v")
  let t = @term_syntax.parse_term(
    "∀ render_slot_0 : Bool, (render_atom_poly : Bool) == render_slot_0",
  )
  inspect(
    @render.layout_statement(t, atoms=[atom]),
    content="∀ (render_slot_0 : Bool), 0v == render_slot_0",
  )
  let arrow = @kernel.mk_type("fun", List([@kernel.bool_ty, @kernel.bool_ty]))
  let function = @kernel.mk_const(
    "render_atom_poly",
    List([(arrow, @kernel.aty)]),
  )
  let other = @kernel.mk_comb(function, @kernel.concl(@bool.truth()))
  assert_eq(
    @render.layout_statement(other, atoms=[atom]),
    @render.layout_statement(other),
  )
  let shadowed = @term_syntax.parse_term(
    "∀ render_atom_poly : Bool, render_atom_poly",
  )
  assert_eq(
    @render.layout_statement(shadowed, atoms=[atom]),
    @render.layout_statement(shadowed),
  )
}

///|
test "joining rendered pieces preserves Unicode reference offsets" {
  let atom = sample_atom(text="🜁w")
  let part = @render.statement(atom.term, atoms=[atom])
  let joined = @render.Statement::join(
    [part, @render.Statement::plain("middle"), part],
    separator="\n🜁\n",
  )
  assert_eq(joined.text, "🜁w\n🜁\nmiddle\n🜁\n🜁w")
  assert_eq(
    joined.canonical,
    part.canonical + "\n🜁\nmiddle\n🜁\n" + part.canonical,
  )
  assert_eq(joined.references.map(r => (r.start, r.length)), [(0, 2), (14, 2)])
  assert_true(
    joined.references.iter().all(r => r.constant == "render_atom_build"),
  )
}

///|
test "atomic configuration rejects open terms and non-atomic text" {
  let atom = sample_atom()
  let variable = @kernel.mk_var("p", @kernel.bool_ty)
  for term in [variable, @kernel.mk_comb(binary("render_atom_open"), variable)] {
    try @render.Atom::new(term, text="32x") catch {
      _ => ()
    } noraise {
      _ => fail("accepted an open term as an atomic rule")
    }
  }
  for text in ["", "32 x", "literal(32)"] {
    try @render.Atom::new(atom.term, text~) catch {
      _ => ()
    } noraise {
      _ => fail("accepted a non-atomic label")
    }
  }
}
