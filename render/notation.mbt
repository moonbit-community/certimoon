// Rendering rules are local values. They never alter HOL's parser or interface.

///|
#derive(Eq)
pub(all) enum Associativity {
  Left
  Right
  NonAssociative
}

///|
pub extend Associativity with Eq::{equal, not_equal}

///|
pub struct Infix {
  constant : @kernel.Term
  symbol : String
  precedence : Int32
  associativity : Associativity
}

///|
/// Display a binary application of this exact typed constant as an infix.
/// Larger precedence binds more tightly. Associativity only omits parentheses
/// on the selected side; it never reassociates the kernel's term.
pub fn Infix::new(
  constant : @kernel.Term,
  symbol~ : String,
  precedence~ : Int32,
  associativity~ : Associativity = NonAssociative,
) -> Infix raise {
  guard constant is Const(_, _) else {
    raise Failure("infix notation requires a constant")
  }
  let ty = @kernel.type_of(constant)
  guard ty is Tyapp("fun", args) && args.to_array() is [_, Tyapp("fun", _)] else {
    raise Failure("infix notation requires two arguments")
  }
  guard symbol != "" &&
    symbol.iter().all(c => c > ' ' && !"()[]{},;\"`".contains_char(c)) else {
    raise Failure("invalid infix symbol")
  }
  guard 0 < precedence && precedence < 1000 else {
    raise Failure("infix precedence must be between 1 and 999")
  }
  { constant, symbol, precedence, associativity, }
}

///|
/// A reference in displayed text; offsets count Unicode scalar values.
pub(all) struct Reference {
  start : Int32
  length : Int32
  constant : String
}

///|
/// A statement's readable text, its original layout, and notation references.
pub struct Statement {
  text : String
  canonical : String
  references : Array[Reference]
}

///|
priv struct Decorated {
  text : String
  precedence : Int32
  rule : Infix?
}

///|
fn identifier_char(c : Char) -> Bool {
  c is ('a'..<='z' | 'A'..<='Z' | '0'..<='9' | '_' | '\'')
}

///|
/// Replace whole identifier tokens only, leaving strings and raw names intact.
fn replace_slots(text : String, slots : Array[(String, String)]) -> String {
  let cs = text.to_array()
  let out = StringBuilder()
  let mut i = 0
  while i < cs.length() {
    let start = i
    if cs[i] == '"' || cs[i] == '`' {
      let quote = cs[i]
      i += 1
      while i < cs.length() {
        let c = cs[i]
        i += 1
        if c == '\\' && i < cs.length() {
          i += 1
        } else if c == quote {
          break
        }
      }
      out.write_string(String::from_array(cs[start:i].to_owned()))
    } else if identifier_char(cs[i]) {
      while i < cs.length() && identifier_char(cs[i]) {
        i += 1
      }
      let name = String::from_array(cs[start:i].to_owned())
      match slots.iter().find_first(s => s.0 == name) {
        Some((_, replacement)) => out.write_string(replacement)
        None => out.write_string(name)
      }
    } else {
      out.write_char(cs[i])
      i += 1
    }
  }
  out.to_string()
}

///|
fn context(
  scope : Array[(String, @kernel.HolType)],
) -> @list.List[(String, @preterm.Pretype)] {
  List(scope.map(v => (v.0, @preterm.pretype_of_type(v.1))))
}

///|
fn in_scope(
  scope : Array[(String, @kernel.HolType)],
  v : @kernel.Term,
) -> Array[(String, @kernel.HolType)] raise {
  let (name, ty) = @kernel.dest_var(v)
  scope.filter(v => v.0 != name) + [(name, ty)]
}

///|
/// Conservative for built-in syntax, whose fixity belongs to term_syntax.
fn atomic_text(text : String) -> Bool raise {
  let (ts, _) = tokens(text.to_array(), 0, None)
  ts
  .iter()
  .all(t => {
    match t {
      TGroup(_, _, _) => true
      TWord(s) => !s.trim().contains(" ")
      _ => false
    }
  })
}

///|
fn operand(d : Decorated, parent : Infix, left : Bool) -> String {
  let same = d.rule is Some(r) && r.constant == parent.constant
  let side = if left {
    parent.associativity == Left
  } else {
    parent.associativity == Right
  }
  if d.precedence > parent.precedence ||
    (d.precedence == parent.precedence && same && side) {
    d.text
  } else {
    "(" + d.text + ")"
  }
}

///|
fn decorate(
  t : @kernel.Term,
  scope : Array[(String, @kernel.HolType)],
  marks : Array[Mark],
) -> Decorated raise {
  if atom_mark(t, marks) is Some(mark) {
    return { text: mark.token, precedence: 1000, rule: None, }
  }
  let (head, args) = @basics.strip_comb(t)
  let args = args.to_array()
  if args.length() >= 2 && infix_mark(head, marks) is Some((mark, rule)) {
    let left = operand(decorate(args[0], scope, marks), rule, true)
    let right = operand(decorate(args[1], scope, marks), rule, false)
    let binary = left + " " + mark.token + " " + right
    if args.length() == 2 {
      return { text: binary, precedence: rule.precedence, rule: Some(rule), }
    }
    let rest = args[2:].map(a => decorate(a, scope, marks).text).join(", ")
    return {
      text: "(" + binary + ")(" + rest + ")",
      precedence: 1000,
      rule: None,
    }
  }
  if !has_notation(t, marks) {
    let text = print_operand(t, scope)
    return {
      text,
      precedence: if atomic_text(text) {
        1000
      } else {
        0
      },
      rule: None,
    }
  }
  // Replace complete notation subterms by fresh, typed slots. The existing
  // printer remains responsible for every other syntactic form and binder.
  let slots : Array[(String, @kernel.Term, String)] = []
  let taken : Set[String] = Set(scope.map(v => v.0))
  fn names(t : @kernel.Term) -> Unit {
    match t {
      Var(n, _) | Const(n, _) => taken.add(n) |> ignore
      Comb(f, x) => {
        names(f)
        names(x)
      }
      Abs(v, b) => {
        names(v)
        names(b)
      }
    }
  }
  names(t)
  fn rewrite(
    t : @kernel.Term,
    scope : Array[(String, @kernel.HolType)],
  ) -> @kernel.Term raise {
    let (f, xs) = @basics.strip_comb(t)
    let is_atom = atom_mark(t, marks) is Some(_)
    if is_atom || (xs.length() >= 2 && infix_mark(f, marks) is Some(_)) {
      let d = decorate(t, scope, marks)
      let mut n = slots.length()
      let mut name = "render_slot_\{n}"
      while taken.contains(name) {
        n += 1
        name = "render_slot_\{n}"
      }
      taken.add(name) |> ignore
      slots.push((name, t, if is_atom { d.text } else { "(" + d.text + ")" }))
      return @kernel.mk_var(name, @kernel.type_of(t))
    }
    match t {
      Comb(f, x) => @kernel.mk_comb(rewrite(f, scope), rewrite(x, scope))
      Abs(v, b) => @kernel.mk_abs(v, rewrite(b, in_scope(scope, v)))
      _ => t
    }
  }
  let replaced = rewrite(t, scope)
  let inner_scope = scope + slots.map(s => (s.0, @kernel.type_of(s.1)))
  let env = context(inner_scope)
  let printed = print_operand(replaced, inner_scope) catch {
    @term_syntax.Unprintable(_) as err => {
      // Match syntax may rename internal pattern binders. When rendering
      // literals, closed slots can be restored under either spelling
      // without capturing variables. Keep infix-only printing unchanged.
      guard marks.iter().any(m => m.rule is Atom(_)) &&
        slots.iter().all(s => @kernel.frees(s.1).is_empty()) else {
        raise err
      }
      print_operand(replaced, inner_scope, exact=false)
    }
    err => raise err
  }
  // Restore structurally under the unchanged binders, then check against the
  // original term. Capture-avoiding substitution would change this operation.
  fn restore(t : @kernel.Term) -> @kernel.Term raise {
    match t {
      Var(n, _) =>
        match slots.iter().find_first(s => s.0 == n) {
          Some((_, original, _)) => original
          None => t
        }
      Comb(f, x) => @kernel.mk_comb(restore(f), restore(x))
      Abs(v, b) => @kernel.mk_abs(v, restore(b))
      _ => t
    }
  }
  let back = restore(
    @term_syntax.parse_term_in_context(
      env,
      printed,
      ty=@preterm.pretype_of_type(@kernel.type_of(replaced)),
    ),
  )
  guard @term_syntax.same_term(back, t) else {
    raise Failure("notation did not read back")
  }
  let text = replace_slots(printed, slots.map(s => (s.0, s.2)))
  { text, precedence: if atomic_text(text) { 1000 } else { 0 }, rule: None, }
}

///|
/// Render with local notation rules; without rules the existing output is exact.
/// Failed custom rendering falls back to the original checked layout.
pub fn statement(
  t : @kernel.Term,
  abbreviate~ : (String) -> String = s => s,
  infixes~ : Array[Infix] = [],
  atoms~ : Array[Atom] = [],
) -> Statement {
  let canonical = layout_with(t, abbreviate, [])
  if infixes.is_empty() && atoms.is_empty() {
    return { text: canonical, canonical, references: [], }
  }
  try {
    let marks = notation_marks(t, infixes, atoms)
    if !has_notation(t, marks) {
      return { text: canonical, canonical, references: [], }
    }
    let (text, references) = unmark(layout_with(t, abbreviate, marks), marks)
    if references.is_empty() {
      { text: canonical, canonical, references: [], }
    } else {
      { text, canonical, references, }
    }
  } catch {
    _ => { text: canonical, canonical, references: [], }
  }
}

///|
/// An entry that uses a client-specific display, such as WebAssembly text.
pub fn Statement::plain(text : String) -> Statement {
  { text, canonical: text, references: [], }
}
