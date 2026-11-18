///|
priv enum Notation {
  Infix(Infix)
  Atom(Atom)
}

///|
priv struct Mark {
  char : Char
  token : String
  rule : Notation
}

///|
fn Notation::term(self : Notation) -> @kernel.Term {
  match self {
    Infix(rule) => rule.constant
    Atom(rule) => rule.term
  }
}

///|
fn Notation::text(self : Notation) -> String {
  match self {
    Infix(rule) => rule.symbol
    Atom(rule) => rule.text
  }
}

///|
fn Notation::matches(self : Notation, t : @kernel.Term) -> Bool {
  match self {
    Infix(rule) => t is Comb(Comb(c, _), _) && c == rule.constant
    Atom(rule) => t == rule.term
  }
}

///|
fn notation_marks(
  t : @kernel.Term,
  infixes : Array[Infix],
  atoms : Array[Atom],
) -> Array[Mark] raise {
  let source = @term_syntax.print_term(t)
  let rules = infixes.map(r => Notation::Infix(r)) + atoms.map(r => Atom(r))
  let marks : Array[Mark] = []
  let mut next = 0xE000
  for rule in rules {
    guard !marks
      .iter()
      .any(m => {
        match (m.rule, rule) {
          (Infix(a), Infix(b)) => a.constant == b.constant
          (Atom(a), Atom(b)) => a.term == b.term
          _ => false
        }
      }) else {
      raise Failure("duplicate notation target")
    }
    let mut c = next.unsafe_to_char()
    while source.contains_char(c) ||
          rules.iter().any(r => r.text().contains_char(c)) {
      next += 1
      c = next.unsafe_to_char()
    }
    marks.push({
      char: c,
      token: c.to_string().repeat(rule.text().length()),
      rule,
    })
    next += 1
  }
  marks
}

///|
fn unmark(
  text : String,
  marks : Array[Mark],
) -> (String, Array[Reference]) raise {
  let cs = text.to_array()
  let out = StringBuilder()
  let references = []
  for i = 0, offset = 0; i < cs.length(); {
    match marks.iter().find_first(m => m.char == cs[i]) {
      Some(m) => {
        let symbol = m.rule.text()
        let length = symbol.to_array().length()
        let (head, _) = @basics.strip_comb(m.rule.term())
        let (name, _) = @kernel.dest_const(head)
        references.push({ start: offset, length, constant: name, })
        out.write_string(symbol)
        continue i + m.token.length(), offset + length
      }
      None => {
        out.write_char(cs[i])
        continue i + 1, offset + 1
      }
    }
  }
  (out.to_string(), references)
}

///|
fn infix_mark(head : @kernel.Term, marks : Array[Mark]) -> (Mark, Infix)? {
  for mark in marks {
    if mark.rule is Infix(rule) && rule.constant == head {
      return Some((mark, rule))
    }
  }
  None
}

///|
fn atom_mark(t : @kernel.Term, marks : Array[Mark]) -> Mark? {
  marks.iter().find_first(m => m.rule is Atom(rule) && rule.term == t)
}

///|
fn has_notation(t : @kernel.Term, marks : Array[Mark]) -> Bool {
  if marks.iter().any(m => m.rule.matches(t)) {
    return true
  }
  match t {
    Comb(f, x) => has_notation(f, marks) || has_notation(x, marks)
    Abs(_, b) => has_notation(b, marks)
    _ => false
  }
}
