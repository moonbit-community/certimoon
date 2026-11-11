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
// A statement with no hypotheses is `∀ (x y : T), body`; a conjunction
// with neither (a definition's equations) has a conjunct per line, `&&`
// before each but the first; any other is printed as it was.
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
    return layout_conjuncts(t, abbr)
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
/// A conjunction (a definition's equations) with a conjunct per line,
/// `&&` before each but the first, if it reads back as `t`.
fn layout_conjuncts(
  t : @kernel.Term,
  abbr : (String) -> String,
) -> String? raise {
  let parts = conj_parts(t)
  if parts.length() < 2 {
    return None
  }
  let printed = parts.map(p => print_in(p, [], abbr))
  let back = @term_syntax.parse_term(rejoin(printed.map(p => p.syntax), "&&"))
  guard @term_syntax.same_term(back, t) else { return None }
  Some(
    printed.mapi((i, p) => (if i == 0 { "" } else { "&& " }) + p.shown).join("\n"),
  )
}

///|
/// `t` for a listing: laid out with its variables and hypotheses (see the
/// top of this file), or else as `print_term` prints it, with its long
/// lines broken (see "Long lines"). `abbreviate` shortens the printed
/// types (it is applied before lines are measured).
pub fn layout_statement(
  t : @kernel.Term,
  abbreviate? : (String) -> String = abbreviate_types,
) -> String {
  let laid = layout_sequent(t, abbreviate) catch { _ => None }
  let text = match laid {
    Some(s) => s
    None =>
      abbreviate(
        @term_syntax.print_term(t) catch {
          _ => (try @printer.string_of_term(t) catch { _ => "?" })
        },
      )
  }
  break_lines(text)
}

// Long lines. A line longer than 80 characters is broken by the structure
// of its text: a call or list that does not fit gets an argument per line,
// indented by two, its closing bracket after the last (and a `match` a
// case per line); a lambda that does
// not fit gets its body on the lines after its binders, indented by two; a
// chain of `&&` (or `||`) a conjunct per line, `&&` first; an equation
// its right side on the next line, `==` first and indented by two, if it
// fits there; a list as many elements to a line as fit; a binder
// (`∃ x : T,`) its body on the next line. Only whitespace changes: a space
// becomes a line break and indentation, or a break follows an opening
// bracket. `break_line` checks that the text is the same without its
// whitespace, and keeps a line it cannot break as it was.

///|
/// A token of a printed line: text, an operator with the spaces around it
/// (`&&`, `||`, `=>`, `==`), a comma, a semicolon (between a `match`'s cases), or
/// a bracketed group.
priv enum Tok {
  TWord(String)
  TSep(String)
  TComma
  TSemi
  TGroup(Char, Array[Tok], Char)
}

///|
/// A line's structure, as `break_line` reads it.
priv enum Doc {
  DText(String)
  DCat(Array[Doc])
  DGroup(String, Array[Doc], String, String)
  DOps(String, Array[Doc])
  DLam(Array[String], Doc)
  DBind(String, Doc)
}

///|
fn closer(c : Char) -> Char? {
  match c {
    '(' => Some(')')
    '[' => Some(']')
    '{' => Some('}')
    _ => None
  }
}

///|
/// Whether `cs` has `s` at `i`.
fn chars_at(cs : Array[Char], i : Int32, s : String) -> Bool {
  let mut k = i
  for c in s {
    if k >= cs.length() || cs[k] != c {
      return false
    }
    k = k + 1
  }
  true
}

///|
/// The tokens of `cs` from `i` to the bracket `close` (or the end), and
/// where they stop.
fn tokens(
  cs : Array[Char],
  i : Int32,
  close : Char?,
) -> (Array[Tok], Int32) raise {
  let toks = []
  let word = StringBuilder()
  let flush = () => {
    if word.to_string() != "" {
      toks.push(TWord(word.to_string()))
      word.reset()
    }
  }
  let mut i = i
  while i < cs.length() {
    let c = cs[i]
    if closer(c) is Some(cl) {
      flush()
      let (inner, j) = tokens(cs, i + 1, Some(cl))
      toks.push(TGroup(c, inner, cl))
      i = j + 1
    } else if c == ')' || c == ']' || c == '}' {
      flush()
      guard close == Some(c) else { raise Failure("tokens: unbalanced") }
      return (toks, i)
    } else if c == ',' || c == ';' {
      flush()
      toks.push(if c == ',' { TComma } else { TSemi })
      i = i + 1
    } else if chars_at(cs, i, " && ") ||
      chars_at(cs, i, " || ") ||
      chars_at(cs, i, " => ") ||
      chars_at(cs, i, " == ") {
      flush()
      toks.push(TSep(String::from_array([cs[i + 1], cs[i + 2]])))
      i = i + 4
    } else {
      word.write_char(c)
      i = i + 1
    }
  }
  flush()
  guard close is None else { raise Failure("tokens: unbalanced") }
  (toks, i)
}

///|
/// The text of `toks`, as it was.
fn toks_text(toks : Array[Tok]) -> String {
  let buf = StringBuilder()
  for t in toks {
    match t {
      TWord(s) => buf.write_string(s)
      TSep(op) => buf.write_string(" " + op + " ")
      TComma => buf.write_string(",")
      TSemi => buf.write_string(";")
      TGroup(o, inner, c) => {
        buf.write_char(o)
        buf.write_string(toks_text(inner))
        buf.write_char(c)
      }
    }
  }
  buf.to_string()
}

///|
/// `toks` without the spaces at either end.
fn trim_toks(toks : Array[Tok]) -> Array[Tok] {
  let out = toks.copy()
  if out is [TWord(s), ..] {
    let t = s.trim_start(chars=" ").to_owned()
    if t == "" {
      out.remove(0) |> ignore
    } else {
      out[0] = TWord(t)
    }
  }
  if out is [.., TWord(s)] {
    let t = s.trim_end(chars=" ").to_owned()
    if t == "" {
      out.pop() |> ignore
    } else {
      out[out.length() - 1] = TWord(t)
    }
  }
  out
}

///|
/// `toks` split where `at` holds, outside brackets.
fn split_toks(toks : Array[Tok], at : (Tok) -> Bool) -> Array[Array[Tok]] {
  let parts = [[]]
  for t in toks {
    if at(t) {
      parts.push([])
    } else {
      parts[parts.length() - 1].push(t)
    }
  }
  parts
}

///|
/// The number of binders (`∀`, `∃`, `ε`) in `toks` outside brackets: each
/// takes the next comma for itself.
fn binders_in(t : Tok) -> Int32 {
  match t {
    TWord(s) => {
      let mut n = 0
      for c in s {
        if c == '∀' || c == '∃' || c == 'ε' {
          n = n + 1
        }
      }
      n
    }
    _ => 0
  }
}

///|
/// The arguments of a group: split at its commas, except those of binders;
/// a `match`'s cases (in braces) at its semicolons.
fn group_args(open : Char, inner : Array[Tok]) -> Array[Doc] raise {
  if trim_toks(inner).is_empty() {
    return []
  }
  if open == '{' {
    return split_toks(inner, t => t is TSemi).map(doc_of)
  }
  let args = [[]]
  let mut pending = 0
  for t in inner {
    if t is TComma && pending == 0 {
      args.push([])
    } else {
      if t is TComma {
        pending = pending - 1
      }
      pending = pending + binders_in(t)
      args[args.length() - 1].push(t)
    }
  }
  args.map(doc_of)
}

///|
/// The structure of a segment of a line (a whole line, or an argument).
fn doc_of(toks : Array[Tok]) -> Doc raise {
  let toks = trim_toks(toks)
  // a binder: its variables to the first comma, then its body
  if toks is [TWord(w), ..] &&
    (w.has_prefix("∀") || w.has_prefix("∃") || w.has_prefix("ε")) {
    match toks.search_by(t => t is TComma) {
      Some(k) => {
        let rest = Array::makei(toks.length() - k - 1, i => toks[k + 1 + i])
        return DBind(
          toks_text(Array::makei(k, i => toks[i])) + ",",
          doc_of(rest),
        )
      }
      None => ()
    }
  }
  let lams = split_toks(toks, t => t is TSep("=>"))
  if lams.length() > 1 {
    let binders = lams[:lams.length() - 1].to_owned().map(trim_toks)
    if binders.iter().all(b => b is [TGroup('(', _, _)]) {
      return DLam(binders.map(toks_text), doc_of(lams[lams.length() - 1]))
    }
    return DText(toks_text(toks))
  }
  for op in ["||", "&&", "=="] {
    let parts = split_toks(toks, t => t is TSep(o) && o == op)
    if parts.length() > 1 {
      return DOps(op, parts.map(doc_of))
    }
  }
  DCat(
    toks.map(t => {
      match t {
        TGroup('{', inner, _) => DGroup("{ ", group_args('{', inner), ";", " }")
        TGroup(o, inner, c) =>
          DGroup(o.to_string(), group_args(o, inner), ",", c.to_string())
        t => DText(toks_text([t]))
      }
    }),
  )
}

///|
/// `d` on one line.
fn flat(d : Doc) -> String {
  match d {
    DText(s) => s
    DCat(ds) => ds.map(flat).join("")
    DGroup(o, args, sep, c) => o + args.map(flat).join(sep + " ") + c
    DOps(op, parts) => parts.map(flat).join(" " + op + " ")
    DLam(bs, body) => bs.join(" => ") + " => " + flat(body)
    DBind(head, body) => head + " " + flat(body)
  }
}

///|
/// The column after `s` is written from column `col`.
fn col_after(s : String, col : Int32) -> Int32 {
  match s.rev_find("\n") {
    Some(k) => s.length() - k - 1
    None => col + s.length()
  }
}

///|
/// `d` written from column `col`, in lines of at most `width` characters
/// where it can be broken; its lines after the first are indented by at
/// least `indent`.
fn render(d : Doc, indent : Int32, col : Int32, width : Int32) -> String {
  let one = flat(d)
  if col + one.length() <= width {
    return one
  }
  let nl = (n : Int32) => "\n" + " ".repeat(n)
  match d {
    DText(s) => s
    DCat(ds) => {
      let buf = StringBuilder()
      let mut c = col
      for x in ds {
        let s = render(x, indent, c, width)
        buf.write_string(s)
        c = col_after(s, c)
      }
      buf.to_string()
    }
    DGroup("[", args, sep, c) if args.length() > 1 &&
      args.iter().all(a => indent + 2 + flat(a).length() <= width) => {
      // a list whose elements each fit on a line: as many to a line as
      // fit, the lines after the first under the first element
      let buf = StringBuilder()
      buf.write_string("[")
      let mut k = col + 1
      for i, a in args {
        let piece = flat(a) + (if i < args.length() - 1 { sep } else { c })
        if i > 0 && k + 1 + piece.length() > width {
          buf.write_string(nl(indent + 1))
          k = indent + 1
        } else if i > 0 {
          buf.write_string(" ")
          k = k + 1
        }
        buf.write_string(piece)
        k = k + piece.length()
      }
      buf.to_string()
    }
    DGroup(o, args, sep, c) => {
      if args.is_empty() {
        return one
      }
      let buf = StringBuilder()
      buf.write_string(o.trim_end(chars=" ").to_owned())
      for i, a in args {
        // (less one for the comma or the closing bracket after it)
        buf.write_string(
          nl(indent + 2) + render(a, indent + 2, indent + 2, width - 1),
        )
        if i < args.length() - 1 {
          buf.write_string(sep)
        }
      }
      buf.write_string(c)
      buf.to_string()
    }
    DOps("==", [l, r]) if indent + 5 + flat(r).length() > width => {
      // an equation whose right side would not fit on a line of its own
      // keeps it after the left side, to break as it needs
      let left = render(l, indent, col, width)
      let c = col_after(left, col) + 4
      left + " == " + render(r, indent, c, width)
    }
    DOps(op, parts) => {
      // an equation's right side under its left, indented by two
      let at = if op == "==" { indent + 2 } else { indent }
      let buf = StringBuilder()
      buf.write_string(render(parts[0], indent, col, width))
      let k = at + op.length() + 1
      for p in parts[1:] {
        buf.write_string(nl(at) + op + " " + render(p, k, k, width))
      }
      buf.to_string()
    }
    DLam(bs, body) => {
      let buf = StringBuilder()
      let mut c = col
      for i, b in bs {
        let piece = b + " =>"
        if i > 0 && c + 1 + piece.length() > width {
          buf.write_string(nl(indent))
          c = indent
        } else if i > 0 {
          buf.write_string(" ")
          c = c + 1
        }
        buf.write_string(piece)
        c = c + piece.length()
      }
      buf.write_string(
        nl(indent + 2) + render(body, indent + 2, indent + 2, width),
      )
      buf.to_string()
    }
    DBind(head, body) =>
      head + nl(indent + 2) + render(body, indent + 2, indent + 2, width)
  }
}

///|
/// `s` without its whitespace.
fn squeeze(s : String) -> String {
  let buf = StringBuilder()
  for c in s {
    if c != ' ' && c != '\n' {
      buf.write_char(c)
    }
  }
  buf.to_string()
}

///|
/// `line` broken into lines of at most `width` characters where its
/// structure allows (see above). What starts it, its indentation and a
/// hypothesis's number or a conjunct's `&&`, stays, and the lines after
/// the first are indented past it.
fn break_line(line : String, width~ : Int32 = 80) -> String {
  if line.length() <= width || line.contains("\"") {
    return line
  }
  let cs = line.to_array()
  let mut p = 0
  while p < cs.length() && cs[p] == ' ' {
    p = p + 1
  }
  let mut q = p
  while q < cs.length() && cs[q] >= '0' && cs[q] <= '9' {
    q = q + 1
  }
  if q > p && chars_at(cs, q, ". ") {
    p = q + 2
  } else if chars_at(cs, p, "&& ") || chars_at(cs, p, "|| ") {
    p = p + 3
  }
  let head = String::from_array(cs[:p].to_owned())
  let body = String::from_array(cs[p:].to_owned())
  let broken = try {
    let (toks, _) = tokens(body.to_array(), 0, None)
    head + render(doc_of(toks), p, p, width)
  } catch {
    _ => line
  }
  if squeeze(broken) == squeeze(line) {
    broken
  } else {
    line
  }
}

///|
/// `text` with each long line broken (`break_line`).
fn break_lines(text : String) -> String {
  let lines : Array[String] = text
    .split("\n")
    .map(l => break_line(l.to_owned()))
    .collect()
  lines.join("\n")
}
