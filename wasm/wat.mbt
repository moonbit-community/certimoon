// WebAssembly's text format, for the listings: a program's code (a list of
// basic instructions, `List[B_e]`) printed one instruction per line, the
// bodies of blocks, loops and ifs indented, as in a .wat file. The text is
// printed from the kernel's term and read back (`code_of_wat`), and
// `wat_of_code` fails unless that gives the same term, so the listing can
// be read instead of the term.
//
// Instructions without a WebAssembly name here (floats, vectors, tables,
// ...) are printed in the term syntax after `hol`, and read back as such.

///|
/// Instructions with no immediates: the term syntax's text and
/// WebAssembly's name.
fn plain_instrs() -> Array[(String, String)] {
  let out = [
    ("Unreachable", "unreachable"),
    ("Nop", "nop"),
    ("Drop", "drop"),
    ("Select(NONE)", "select"),
    ("Return", "return"),
    ("Memory_size", "memory.size"),
    ("Memory_grow", "memory.grow"),
  ]
  let signed = (op : String, name : String) => [
    (op + "(S)", name + "_s"),
    (op + "(U)", name + "_u"),
  ]
  for t in ["i32", "i64"] {
    let tn = "T_" + t
    for u in [("Clz", "clz"), ("Ctz", "ctz"), ("Popcnt", "popcnt")] {
      out.push(("Unop(\{tn}, Unop_i(\{u.0}))", "\{t}.\{u.1}"))
    }
    let extends = if t == "i32" { ["8", "16"] } else { ["8", "16", "32"] }
    for k in extends {
      out.push(("Unop(\{tn}, Extend_s(Tp_i\{k}))", "\{t}.extend\{k}_s"))
    }
    out.push(("Testop(\{tn}, Eqz)", "\{t}.eqz"))
    let binops = [("Add", "add"), ("Sub", "sub"), ("Mul", "mul")] +
      signed("Div", "div") +
      signed("Rem", "rem") +
      [("And", "and"), ("Or", "or"), ("Xor", "xor"), ("Shl", "shl")] +
      signed("Shr", "shr") +
      [("Rotl", "rotl"), ("Rotr", "rotr")]
    for b in binops {
      out.push(("Binop(\{tn}, Binop_i(\{b.0}))", "\{t}.\{b.1}"))
    }
    let relops = [("Eq", "eq"), ("Ne", "ne")] +
      signed("Lt", "lt") +
      signed("Gt", "gt") +
      signed("Le", "le") +
      signed("Ge", "ge")
    for r in relops {
      out.push(("Relop(\{tn}, Relop_i(\{r.0}))", "\{t}.\{r.1}"))
    }
  }
  out
}

///|
/// Instructions with one index: the constructor and WebAssembly's name.
let index_instrs : Array[(String, String)] = [
  ("Local_get", "local.get"),
  ("Local_set", "local.set"),
  ("Local_tee", "local.tee"),
  ("Global_get", "global.get"),
  ("Global_set", "global.set"),
  ("Br", "br"),
  ("Br_if", "br_if"),
  ("Call", "call"),
]

///|
/// Loads and stores: the type and packing as the term syntax writes them,
/// and WebAssembly's name.
let load_instrs : Array[(String, String, String)] = [
  ("T_i32", "NONE", "i32.load"),
  ("T_i64", "NONE", "i64.load"),
  ("T_i32", "SOME((Tp_i8, S))", "i32.load8_s"),
  ("T_i32", "SOME((Tp_i8, U))", "i32.load8_u"),
  ("T_i32", "SOME((Tp_i16, S))", "i32.load16_s"),
  ("T_i32", "SOME((Tp_i16, U))", "i32.load16_u"),
  ("T_i64", "SOME((Tp_i8, S))", "i64.load8_s"),
  ("T_i64", "SOME((Tp_i8, U))", "i64.load8_u"),
  ("T_i64", "SOME((Tp_i16, S))", "i64.load16_s"),
  ("T_i64", "SOME((Tp_i16, U))", "i64.load16_u"),
  ("T_i64", "SOME((Tp_i32, S))", "i64.load32_s"),
  ("T_i64", "SOME((Tp_i32, U))", "i64.load32_u"),
]

///|
let store_instrs : Array[(String, String, String)] = [
  ("T_i32", "NONE", "i32.store"),
  ("T_i64", "NONE", "i64.store"),
  ("T_i32", "SOME(Tp_i8)", "i32.store8"),
  ("T_i32", "SOME(Tp_i16)", "i32.store16"),
  ("T_i64", "SOME(Tp_i8)", "i64.store8"),
  ("T_i64", "SOME(Tp_i16)", "i64.store16"),
  ("T_i64", "SOME(Tp_i32)", "i64.store32"),
]

///|
/// `t` printed in the term syntax.
fn term_text(t : @kernel.Term) -> String raise {
  @term_syntax.print_term(t)
}

///|
/// A numeral's digits.
fn numeral_text(t : @kernel.Term) -> String raise {
  @basics.dest_numeral(t).to_string()
}

///|
/// A block type as WebAssembly writes it after the block's name (with its
/// leading space), if it is one of those.
fn blocktype_wat(tb : @kernel.Term) -> String? {
  let text = term_text(tb) catch { _ => return None }
  match text {
    "Tbv(NONE)" => Some("")
    _ => {
      for t in ["i32", "i64", "f32", "f64"] {
        if text == "Tbv(SOME(T_num(T_\{t})))" {
          return Some(" (result \{t})")
        }
      }
      let (h, args) = head_args(tb)
      if h == "Tbf" && args.length() == 1 {
        (try Some(" (type " + numeral_text(args[0]) + ")") catch { _ => None })
      } else {
        None
      }
    }
  }
}

///|
/// The lines of the instruction `t` at depth `depth`, onto `out`.
fn instr_lines(
  t : @kernel.Term,
  depth : Int,
  plain : Map[String, String],
  out : Array[String],
) -> Unit raise {
  let pad = "  ".repeat(depth)
  let (h, args) = head_args(t)
  let line = (s : String) => out.push(pad + s)
  let fallback = () => line("hol " + term_text(t))
  match (h, args.length()) {
    ("Block" | "Loop", 2) =>
      match blocktype_wat(args[0]) {
        Some(bt) => {
          line((if h == "Block" { "block" } else { "loop" }) + bt)
          code_lines(args[1], depth + 1, plain, out)
          line("end")
        }
        None => fallback()
      }
    ("If", 3) =>
      match blocktype_wat(args[0]) {
        Some(bt) => {
          line("if" + bt)
          code_lines(args[1], depth + 1, plain, out)
          if !@basics.dest_list(args[2]).is_empty() {
            line("else")
            code_lines(args[2], depth + 1, plain, out)
          }
          line("end")
        }
        None => fallback()
      }
    (_, 1) if index_instrs.search_by(p => p.0 == h) is Some(k) =>
      line(index_instrs[k].1 + " " + numeral_text(args[0]))
    ("EConstNum", 1) => {
      let (c, cargs) = head_args(args[0])
      let (w, wargs) = if cargs.length() == 1 { head_args(cargs[0]) } else { ("", []) }
      match (c, w, wargs.length()) {
        ("ConstInt32", "word", 1) => line("i32.const " + numeral_text(wargs[0]))
        ("ConstInt64", "word", 1) => line("i64.const " + numeral_text(wargs[0]))
        // a word that is not a numeral, in the term syntax
        ("ConstInt32", _, _) if @kernel.is_var(cargs[0]) => line("i32.const " + @kernel.dest_var(cargs[0]).0)
        ("ConstInt64", _, _) if @kernel.is_var(cargs[0]) => line("i64.const " + @kernel.dest_var(cargs[0]).0)
        _ => fallback()
      }
    }
    ("Load" | "Store", 4) => {
      let table = if h == "Load" { load_instrs } else { store_instrs }
      let ty = term_text(args[0])
      // NONE alone prints with its type: compare by the constructor
      let pk = match head_args(args[1]) {
        ("NONE", _) => "NONE"
        ("SOME", [x]) => "SOME(" + term_text(x) + ")"
        _ => term_text(args[1])
      }
      match table.search_by(e => e.0 == ty && e.1 == pk) {
        Some(k) => {
          let a = @basics.dest_numeral(args[2]).to_string()
          line(table[k].2 + " offset=" + numeral_text(args[3]) + " align=2**" + a)
        }
        None => fallback()
      }
    }
    _ =>
      match plain.get(term_text(t)) {
        Some(name) => line(name)
        None => fallback()
      }
  }
}

///|
/// The lines of the list of instructions `code` at depth `depth`.
fn code_lines(
  code : @kernel.Term,
  depth : Int,
  plain : Map[String, String],
  out : Array[String],
) -> Unit raise {
  for t in @basics.dest_list(code) {
    instr_lines(t, depth, plain, out)
  }
}

///|
/// `code` (a list of basic instructions) in WebAssembly's text format,
/// one instruction per line, each line after `indent`. Fails unless the
/// text reads back (`code_of_wat`) as `code`.
pub fn wat_of_code(code : @kernel.Term, indent? : String = "") -> String raise {
  let plain : Map[String, String] = Map([])
  for p in plain_instrs() {
    plain[term_text(@term_syntax.parse_term(p.0))] = p.1
  }
  let lines = []
  code_lines(code, 0, plain, lines)
  let text = lines.map(l => indent + l).join("\n")
  let back = code_of_wat(text)
  guard @term_syntax.same_term(back, code) else {
    raise Failure("wasmcert/wasm: wat_of_code: the text does not read back as the code:\n" + text)
  }
  text
}

///|
/// The term syntax's text of the instructions in `lines` from `start`, up
/// to an `end` or `else` at this level (or the last line): the texts, and
/// where the reading stopped.
fn read_instrs(lines : Array[String], start : Int) -> (Array[String], Int) raise {
  let plain : Map[String, String] = Map([])
  for p in plain_instrs() {
    plain[p.1] = p.0
  }
  let out = []
  let mut i = start
  while i < lines.length() {
    let line = lines[i]
    if line == "end" || line == "else" {
      break
    }
    let (word, rest) = match line.find(" ") {
      Some(k) => (line[:k].to_owned(), line[k + 1:].to_owned())
      None => (line, "")
    }
    let blocktype = () => match rest {
      "" => "Tbv(NONE)"
      _ =>
        if rest.has_prefix("(result ") && rest.has_suffix(")") {
          "Tbv(SOME(T_num(T_" + rest[8:rest.length() - 1].to_owned() + ")))"
        } else if rest.has_prefix("(type ") && rest.has_suffix(")") {
          "Tbf(" + rest[6:rest.length() - 1].to_owned() + ")"
        } else {
          raise Failure("wasmcert/wasm: code_of_wat: block type " + rest)
        }
    }
    let list = (xs : Array[String]) => if xs.is_empty() { "NIL" } else { "[" + xs.join(", ") + "]" }
    let expect_end = (k : Int) => if k >= lines.length() || lines[k] != "end" {
      raise Failure("wasmcert/wasm: code_of_wat: no end for line " + (start + 1).to_string())
    }
    match word {
      "block" | "loop" => {
        let (body, k) = read_instrs(lines, i + 1)
        expect_end(k)
        let c = if word == "block" { "Block" } else { "Loop" }
        out.push(c + "(" + blocktype() + ", " + list(body) + ")")
        i = k + 1
      }
      "if" => {
        let (then_, k) = read_instrs(lines, i + 1)
        let (else_, k) = if k < lines.length() && lines[k] == "else" {
          read_instrs(lines, k + 1)
        } else {
          ([], k)
        }
        expect_end(k)
        out.push("If(" + blocktype() + ", " + list(then_) + ", " + list(else_) + ")")
        i = k + 1
      }
      "hol" => {
        out.push(rest)
        i = i + 1
      }
      "i32.const" | "i64.const" => {
        let c = if word == "i32.const" { "ConstInt32" } else { "ConstInt64" }
        // digits are a numeral's word; anything else is the term itself
        let digits = rest != "" && rest.iter().all(ch => ch >= '0' && ch <= '9')
        out.push("EConstNum(" + c + "(" + (if digits { "word(" + rest + ")" } else { rest }) + "))")
        i = i + 1
      }
      _ => {
        if index_instrs.search_by(p => p.1 == word) is Some(k) {
          out.push(index_instrs[k].0 + "(" + rest + ")")
        } else if load_instrs.search_by(e => e.2 == word) is Some(k) {
          out.push("Load(" + load_instrs[k].0 + ", " + load_instrs[k].1 + ", " + memarg(rest) + ")")
        } else if store_instrs.search_by(e => e.2 == word) is Some(k) {
          out.push("Store(" + store_instrs[k].0 + ", " + store_instrs[k].1 + ", " + memarg(rest) + ")")
        } else if plain.get(line) is Some(t) {
          out.push(t)
        } else {
          raise Failure("wasmcert/wasm: code_of_wat: unknown instruction " + line)
        }
        i = i + 1
      }
    }
  }
  (out, i)
}

///|
/// `offset=O align=2**A` as the term syntax's `A, O`.
fn memarg(s : String) -> String raise {
  match s.split(" ").collect() {
    [o, a] if o.has_prefix("offset=") && a.has_prefix("align=2**") =>
      a[9:].to_owned() + ", " + o[7:].to_owned()
    _ => raise Failure("wasmcert/wasm: code_of_wat: memory argument " + s)
  }
}

///|
/// The code a text printed by `wat_of_code` stands for (indentation
/// aside).
pub fn code_of_wat(text : String) -> @kernel.Term raise {
  let lines = text.split("\n").map(l => l.trim().to_owned()).filter(l => l != "").collect()
  let (instrs, k) = read_instrs(lines, 0)
  if k != lines.length() {
    raise Failure("wasmcert/wasm: code_of_wat: unexpected " + lines[k])
  }
  @term_syntax.parse_term("[" + instrs.join(", ") + "]")
}
