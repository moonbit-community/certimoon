// Statements laid out for reading. A statement `∀ xs, H1 && ... && Hn → C`
// is shown as its variables grouped by type, then `if` and the numbered
// hypotheses, then `then` and the conclusion, one alternative per `or`:
//
//   ∀ (s s2 : Wstore) (f f2 : Wframe) (vs : List[Value])
//   if
//     1. s_funcs(s) == fs
//     2. reduce_trans(...)
//   then
//     ∃ (vs2 : List[Value]),
//       es2 == MAP(v_to_e, vs2)
//       && lift(q, r, s2, f2, vs2)
//   or
//     ...
//
// A statement with no hypotheses is `∀ (x y : T), body`, and one with no
// variables or hypotheses is printed as it was.
//
// Each hypothesis and each conjunct is printed by `print_term` (under the
// variables it uses, which are then cut off, so that their types are not
// repeated); only the glue between the pieces is this file's. So that the
// glue cannot change what is shown, `layout_statement` also writes the
// statement back from the same printed pieces in the term syntax, parses
// that and checks that it is the kernel's statement. If it is not, the
// statement is printed on one line, as `print_term` prints it.

///|
/// One step of a statement's prefix: a variable bound by `∀`, or an
/// implication whose antecedent is the hypotheses from `first` to `last`.
priv enum Step {
  Bind(String, @kernel.HolType)
  Assume(Int, Int)
}

///|
/// A printed piece: as shown, and in the term syntax (parenthesized).
priv struct Piece {
  shown : String
  syntax : String
}

///|
/// The parts of `t` along its right-nested `&&` (`A && (B && C)` gives A,
/// B, C; a conjunction on the left stays one part).
fn conj_parts(t : @kernel.Term) -> Array[@kernel.Term] raise {
  let parts = []
  let mut t = t
  while @basics.is_conj(t) {
    let (a, b) = @basics.dest_conj(t)
    parts.push(a)
    t = b
  }
  parts.push(t)
  parts
}

///|
/// The parts of `t` along its right-nested `||`.
fn disj_parts(t : @kernel.Term) -> Array[@kernel.Term] raise {
  let parts = []
  let mut t = t
  while @basics.is_disj(t) {
    let (a, b) = @basics.dest_disj(t)
    parts.push(a)
    t = b
  }
  parts.push(t)
  parts
}

///|
/// `parts` joined by `op`, nested to the right as `conj_parts` reads them.
fn rejoin(parts : Array[String], op : String) -> String {
  let mut s = parts[parts.length() - 1]
  for i = parts.length() - 2; i >= 0; i = i - 1 {
    s = "(" + parts[i] + " " + op + " " + s + ")"
  }
  s
}

///|
/// `vars` bound by `q` (`∀` or `∃`) around `body`, in the term syntax.
fn bind_syntax(
  q : String,
  vars : Array[(String, @kernel.HolType)],
  body : String,
) -> String raise {
  let mut s = body
  for i = vars.length() - 1; i >= 0; i = i - 1 {
    let (n, ty) = vars[i]
    s = "(" + q + " " + n + " : " + @term_syntax.print_type(ty) + ", " + s + ")"
  }
  s
}

///|
/// `t` printed where `scope` is bound: under a `∀` of each variable of
/// `scope` it uses, which is then cut off.
fn print_in(
  t : @kernel.Term,
  scope : Array[(String, @kernel.HolType)],
  abbr : (String) -> String,
) -> Piece raise {
  let free = @kernel.frees(t).to_array()
  let used = scope.filter(v => free.iter().any(x => x is Var(n, ty) && n == v.0 && ty == v.1))
  let mut wrapped = t
  let mut prefix = ""
  for i = used.length() - 1; i >= 0; i = i - 1 {
    let (n, ty) = used[i]
    wrapped = @bool.mk_forall(@kernel.mk_var(n, ty), wrapped)
    prefix = "∀ " + n + " : " + @term_syntax.print_type(ty) + ", " + prefix
  }
  let s = @term_syntax.print_term(wrapped)
  guard s.has_prefix(prefix) else {
    raise Failure("print_in: the variables were renamed")
  }
  let text = s[prefix.length():].to_owned()
  { shown: abbr(text), syntax: "(" + text + ")" }
}

///|
/// Variables grouped by type, in the order their types first appear:
/// `(s s2 : Wstore)`, `(f : Wframe)`.
fn group_vars(
  vars : Array[(String, @kernel.HolType)],
  abbr : (String) -> String,
) -> Array[String] raise {
  let types : Array[String] = []
  let names : Array[Array[String]] = []
  for v in vars {
    let ty = abbr(@term_syntax.print_type(v.1))
    match types.search(ty) {
      Some(i) => names[i].push(v.0)
      None => {
        types.push(ty)
        names.push([v.0])
      }
    }
  }
  types.mapi((i, ty) => "(" + names[i].join(" ") + " : " + ty + ")")
}

///|
/// `head` then the groups, separated by spaces, broken before a group that
/// would pass 80 characters; the lines after the first are indented by
/// `indent`.
fn wrap_groups(head : String, groups : Array[String], indent : String) -> String {
  let buf = StringBuilder()
  let mut line = head
  for g in groups {
    if line.length() > head.length() && line.length() + 1 + g.length() > 80 {
      buf.write_string(line + "\n")
      line = indent + g
    } else if line.length() == head.length() {
      line = line + g
    } else {
      line = line + " " + g
    }
  }
  buf.write_string(line)
  buf.to_string()
}

///|
/// Whether each name is bound once and is not in `taken`.
fn all_new(
  vars : Array[(String, @kernel.HolType)],
  taken : Array[String],
) -> Bool {
  let names = vars.map(v => v.0)
  names
  .mapi((i, n) => !taken.contains(n) && names.search(n) == Some(i))
  .iter()
  .all(b => b)
}

///|
/// The variables `t` binds with `∃` at its head, and its body.
fn strip_exists_vars(
  t : @kernel.Term,
) -> (Array[(String, @kernel.HolType)], @kernel.Term) raise {
  let vars = []
  let mut t = t
  while @basics.is_exists(t) {
    let (v, b) = @basics.dest_exists(t)
    vars.push(@kernel.dest_var(v))
    t = b
  }
  (vars, t)
}

///|
/// One alternative of a conclusion, where `scope` is bound and `taken` are
/// the names in use: its lines, indented by two, and its term syntax. An
/// `∃` of new names over a conjunction shows its variables, then a
/// conjunct per line; a conjunction shows a conjunct per line.
fn layout_alternative(
  t : @kernel.Term,
  scope : Array[(String, @kernel.HolType)],
  taken : Array[String],
  abbr : (String) -> String,
) -> Piece raise {
  let (vars, body) = strip_exists_vars(t)
  let parts = conj_parts(body)
  if vars.length() > 0 && parts.length() > 1 && all_new(vars, taken) {
    let inner = scope + vars
    let printed = parts.map(p => print_in(p, inner, abbr))
    let lines = printed.mapi((i, p) => (if i == 0 { "    " } else { "    && " }) +
      p.shown)
    {
      shown: wrap_groups("  ∃ ", group_vars(vars, abbr), "    ") +
      ",\n" +
      lines.join("\n"),
      syntax: bind_syntax("∃", vars, rejoin(printed.map(p => p.syntax), "&&")),
    }
  } else if vars.length() > 0 && all_new(vars, taken) {
    let p = print_in(body, scope + vars, abbr)
    let head = wrap_groups("  ∃ ", group_vars(vars, abbr), "    ") + ","
    let one_line = head + " " + p.shown
    {
      shown: if !head.contains("\n") && one_line.length() <= 100 {
        one_line
      } else {
        head + "\n    " + p.shown
      },
      syntax: bind_syntax("∃", vars, p.syntax),
    }
  } else if vars.length() == 0 && parts.length() > 1 {
    let printed = parts.map(p => print_in(p, scope, abbr))
    let lines = printed.mapi((i, p) => (if i == 0 { "  " } else { "  && " }) +
      p.shown)
    { shown: lines.join("\n"), syntax: rejoin(printed.map(p => p.syntax), "&&") }
  } else {
    let p = print_in(t, scope, abbr)
    { shown: "  " + p.shown, syntax: p.syntax }
  }
}

///|
/// `t` laid out, if it has variables or hypotheses at its head and the
/// layout reads back as `t`.
fn layout_sequent(
  t : @kernel.Term,
  abbr : (String) -> String,
) -> String? raise {
  // the prefix: ∀s and implications, until neither is at the head; a name
  // bound twice would be ambiguous once the variables are shown together
  let steps : Array[Step] = []
  let vars : Array[(String, @kernel.HolType)] = []
  let hyps : Array[@kernel.Term] = []
  let taken : Array[String] = @kernel.frees(t)
    .to_array()
    .map(v => if v is Var(n, _) { n } else { "" })
  let mut body = t
  while true {
    if @basics.is_forall(body) {
      let (v, b) = @basics.dest_forall(body)
      let (n, ty) = @kernel.dest_var(v)
      if taken.contains(n) {
        break
      }
      taken.push(n)
      vars.push((n, ty))
      steps.push(Bind(n, ty))
      body = b
    } else if @basics.is_imp(body) {
      let (a, b) = @basics.dest_imp(body)
      let first = hyps.length()
      for h in conj_parts(a) {
        hyps.push(h)
      }
      steps.push(Assume(first, hyps.length()))
      body = b
    } else {
      break
    }
  }
  if vars.length() == 0 && hyps.length() == 0 {
    return None
  }
  let printed_hyps = hyps.map(h => print_in(h, vars, abbr))
  let conclusion = if hyps.length() == 0 {
    [print_in(body, vars, abbr)]
  } else {
    disj_parts(body).map(d => layout_alternative(d, vars, taken, abbr))
  }
  // what is shown
  let shown = if hyps.length() == 0 {
    let head = wrap_groups("∀ ", group_vars(vars, abbr), "  ") + ","
    let one_line = head + " " + conclusion[0].shown
    if !head.contains("\n") && one_line.length() <= 100 {
      one_line
    } else {
      head + "\n  " + conclusion[0].shown
    }
  } else {
    let buf = StringBuilder()
    if vars.length() > 0 {
      buf.write_string(wrap_groups("∀ ", group_vars(vars, abbr), "  ") + "\n")
    }
    buf.write_string("if\n")
    for i, h in printed_hyps {
      buf.write_string("  \{i + 1}. " + h.shown + "\n")
    }
    buf.write_string("then\n")
    buf.write_string(conclusion.map(a => a.shown).join("\nor\n"))
    buf.to_string()
  }
  // the same in the term syntax, built from the same pieces
  let mut syntax = rejoin(conclusion.map(a => a.syntax), "||")
  for i = steps.length() - 1; i >= 0; i = i - 1 {
    match steps[i] {
      Bind(n, ty) => syntax = bind_syntax("∀", [(n, ty)], syntax)
      Assume(first, last) => {
        let ante = rejoin(
          Array::makei(last - first, i => printed_hyps[first + i].syntax),
          "&&",
        )
        syntax = "(" + ante + " → " + syntax + ")"
      }
    }
  }
  let back = @term_syntax.parse_term(syntax)
  if @term_syntax.same_term(back, t) {
    Some(shown)
  } else {
    None
  }
}

///|
/// `t` for a listing: laid out with its variables and hypotheses (see the
/// top of this file), or else as `print_term` prints it. `abbreviate`
/// shortens the printed types (it is applied before lines are measured).
pub fn layout_statement(
  t : @kernel.Term,
  abbreviate? : (String) -> String = abbreviate_types,
) -> String {
  let laid = layout_sequent(t, abbreviate) catch { _ => None }
  match laid {
    Some(s) => s
    None =>
      abbreviate(
        @term_syntax.print_term(t) catch {
          _ => (try @printer.string_of_term(t) catch { _ => "?" })
        },
      )
  }
}
