///|
// The kernel's definition rule handles a fresh constant applied to distinct
// variable parameters. Keep recursion, patterns, hidden variables/types, and
// existing constants on the general processor (including benign redefinition).
fn is_direct_definition(goal : @kernel.Term) -> Bool raise {
  let (quantified, body) = @basics.strip_forall(goal)
  let equation = (Some(@kernel.dest_eq(body)) catch { _ => None })
  guard equation is Some((lhs, rhs)) else { return false }
  let (head, args) = @basics.strip_comb(lhs)
  if !@kernel.is_var(head) || @kernel.vfree_in(head, rhs) {
    return false
  }
  let seen : Array[@kernel.Term] = []
  for arg in args {
    if !@kernel.is_var(arg) || seen.contains(arg) {
      return false
    }
    seen.push(arg)
  }
  for v in quantified {
    if !seen.contains(v) {
      return false
    }
  }
  for free in @kernel.frees(rhs) {
    if !seen.contains(free) {
      return false
    }
  }
  let allowed_types = @kernel.type_vars_in_term(head).to_array()
  for ty in @kernel.type_vars_in_term(rhs) {
    if !allowed_types.contains(ty) {
      return false
    }
  }
  true
}

///|
fn define_equation(goal : @kernel.Term) -> @kernel.Thm raise {
  if !is_direct_definition(goal) {
    return @define.define_(goal)
  }
  // new_definition quantifies all parameters. define_ retains only the
  // explicit outer quantifiers, leaving other parameters free in its result.
  let (quantified, _) = @basics.strip_forall(goal)
  let th = @bool.genl(quantified, @bool.spec_all(@drule.new_definition(goal)))
  // define_ consults this registry before accepting a benign redefinition.
  @pair.the_definitions().val = @pair.the_definitions().val.prepend(th)
  th
}
