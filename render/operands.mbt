///|
/// Print an operand with the result type known by its enclosing infix.
/// A fresh typed application gives the existing printer that context and
/// keeps its read-back check, without annotating every polymorphic literal.
fn print_operand(
  t : @kernel.Term,
  scope : Array[(String, @kernel.HolType)],
  exact~ : Bool = true,
) -> String raise {
  let taken = scope.map(v => v.0) +
    term_constants(t) +
    @basics.variables(t)
    .to_array()
    .map(v => if v is Var(name, _) { name } else { "" })
  let mut n = 0
  let mut name = "render_operand_\{n}"
  while taken.contains(name) {
    n += 1
    name = "render_operand_\{n}"
  }
  let ty = @kernel.mk_type("fun", List([@kernel.type_of(t), @kernel.bool_ty]))
  let wrapped = @kernel.mk_comb(@kernel.mk_var(name, ty), t)
  let printed = @term_syntax.print_term_in_context(
    context(scope + [(name, ty)]),
    wrapped,
    exact~,
  )
  let prefix = name + "("
  guard printed.has_prefix(prefix) && printed.has_suffix(")") else {
    raise Failure("unexpected operand application layout")
  }
  printed[prefix.length():printed.length() - 1].to_owned()
}
