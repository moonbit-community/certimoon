///|
/// An exact, closed constant application displayed as a single literal.
pub struct Atom {
  term : @kernel.Term
  text : String
}

///|
/// Use `text` for this exact term and type, without changing HOL's parser.
/// The term must be closed and headed by a constant; references identify
/// that constant. The display must be a single token without brackets.
pub fn Atom::new(term : @kernel.Term, text~ : String) -> Atom raise {
  guard @basics.strip_comb(term).0 is Const(_, _) &&
    @kernel.frees(term).is_empty() else {
    raise Failure("atomic notation requires a closed constant application")
  }
  guard text != "" &&
    text.iter().all(c => c > ' ' && !"()[]{},;\"`".contains_char(c)) else {
    raise Failure("invalid atomic notation")
  }
  { term, text, }
}

///|
/// Join rendered pieces while preserving canonical text and symbol offsets.
pub fn Statement::join(
  parts : Array[Statement],
  separator~ : String,
) -> Statement {
  let references = []
  let mut offset = 0
  let gap = separator.to_array().length()
  for part in parts {
    for reference in part.references {
      references.push({
        start: offset + reference.start,
        length: reference.length,
        constant: reference.constant,
      })
    }
    offset += part.text.to_array().length() + gap
  }
  {
    text: parts.map(p => p.text).join(separator),
    canonical: parts.map(p => p.canonical).join(separator),
    references,
  }
}
