// Notation supplied by the Wasm client, using the generic renderer's rules.

///|
let word_operators : Array[(String, String, Int32)] = [
  ("word_add", "+", 50),
  ("word_sub", "−", 50),
  ("word_mul", "×", 60),
  ("word_and", "&", 40),
  ("word_xor", "^", 35),
  ("word_or", "|", 30),
  ("word_jshl", "<<", 45),
  ("word_jshr", ">>", 45),
  ("word_jushr", ">>>", 45),
]

///|
/// Fixed word widths appear as subscripts; an arbitrary width uses ʷ.
fn word_suffix(constant : @kernel.Term) -> String raise {
  let (_, args) = @kernel.dest_type(@kernel.type_of(constant))
  let operand = args.to_array()[0]
  let ty = @term_syntax.print_type(operand) catch { _ => return "ʷ" }
  guard ty.has_prefix("Word[") && ty.has_suffix("]") else { return "ʷ" }
  let width = ty[5:ty.length() - 1].to_owned()
  guard width != "" && width.iter().all(c => c is ('0'..<='9')) else {
    return "ʷ"
  }
  let digits = "₀₁₂₃₄₅₆₇₈₉".to_array()
  let out = StringBuilder()
  for c in width {
    out.write_char(digits[c.to_int() - '0'.to_int()])
  }
  out.to_string()
}

///|
/// Local infix rules for the typed word operators occurring in `t`.
/// Arithmetic wraps at the displayed width. The j-shifts mask their counts
/// modulo that width; >> is signed and >>> is unsigned. The original HOL
/// constants and their type instances remain attached to each symbol.
pub fn word_infixes(t : @kernel.Term) -> Array[@render.Infix] raise {
  let rules = []
  let seen : Array[@kernel.Term] = []
  fn walk(t : @kernel.Term) -> Unit raise {
    match t {
      Const(name, _) => {
        guard !seen.contains(t) else { return }
        guard word_operators.iter().find_first(op => op.0 == name)
          is Some((_, symbol, precedence)) else {
          return
        }
        seen.push(t)
        rules.push(
          @render.Infix::new(
            t,
            symbol=symbol + word_suffix(t),
            precedence~,
            associativity=Left,
          ),
        )
      }
      Comb(f, x) => {
        walk(f)
        walk(x)
      }
      Abs(_, body) => walk(body)
      Var(_, _) => ()
    }
  }
  walk(t)
  rules
}

///|
fn word_literal_text(t : @kernel.Term) -> String? {
  match t {
    Comb(Const("word", _), numeral) =>
      try @basics.dest_numeral(numeral) catch {
        _ => None
      } noraise {
        value => Some(value.to_string() + "w")
      }
    _ => None
  }
}

///|
/// Display numeral applications such as `word(32)` as `32w`.
/// Computed arguments, variables named `word`, and partial applications
/// keep their original syntax. Numeral values are never reduced modulo
/// the word width or converted through a machine integer.
pub fn word_literals(t : @kernel.Term) -> Array[@render.Atom] raise {
  let rules = []
  let seen : Array[@kernel.Term] = []
  fn walk(t : @kernel.Term) -> Unit raise {
    if word_literal_text(t) is Some(text) {
      if !seen.contains(t) {
        seen.push(t)
        rules.push(@render.Atom::new(t, text~))
      }
      return
    }
    match t {
      Comb(f, x) => {
        walk(f)
        walk(x)
      }
      Abs(_, body) => walk(body)
      _ => ()
    }
  }
  walk(t)
  rules
}
