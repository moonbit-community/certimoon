// The listings as data, for a review site (tools/review_site.py): each
// entry with its statement as the listing shows it, the constants its
// statement uses and those it defines, and where in the source it is
// made. `listing_json` here and in package logic write them; their tests
// keep them in __snapshot__/theory.json beside theory.md.

///|
/// The constants of `t`, each once, in the order they first appear.
pub fn term_constants(t : @kernel.Term) -> Array[String] {
  let out : Array[String] = []
  let seen : Set[String] = Set([])
  fn walk(t : @kernel.Term) -> Unit {
    match t {
      Const(n, _) =>
        if !seen.contains(n) {
          seen.add(n)
          out.push(n)
        }
      Var(_, _) => ()
      Comb(f, x) => {
        walk(f)
        walk(x)
      }
      Abs(_, b) => walk(b)
    }
  }
  walk(t)
  out
}

///|
/// The head constant of `t` applied to arguments, if it is one.
fn head_constant(t : @kernel.Term) -> String? {
  match @basics.strip_comb(t).0 {
    Const(n, _) => Some(n)
    _ => None
  }
}

///|
/// The constants a definition, relation or type definition `th` defines:
/// the head of each equation's left side or of each rule's conclusion, or
/// the abstraction and representation functions of a type. Lemmas and
/// examples define none.
pub fn defined_constants(kind : String, th : @kernel.Thm) -> Array[String] {
  let out : Array[String] = []
  let add = (n : String?) => if n is Some(n) && !out.contains(n) {
    out.push(n)
  }
  for c in @basics.conjuncts(@kernel.concl(th)) {
    let body = @basics.strip_forall(c).1
    match kind {
      "definition" | "relation" => {
        // an equation's left side, or a rule's conclusion
        let head = if @basics.is_eq(body) {
          @kernel.dest_eq(body).0 catch { _ => body }
        } else if @basics.is_imp(body) {
          @basics.dest_imp(body).1 catch { _ => body }
        } else {
          body
        }
        add(head_constant(head))
      }
      "type definition" =>
        for n in term_constants(body) {
          if n.has_prefix("mk_") || n.has_prefix("dest_") {
            add(Some(n))
          }
        }
      _ => ()
    }
  }
  out
}

///|
/// One entry as JSON: `kind` ("section" for a heading, whose `name` is the
/// title), `name`, `statement` (as the listing shows it), the constants it
/// `uses` and `defines`, and the `file` and `line` where it is made (from
/// a SourceLoc, `file:line:column-line:column@module`). For a theorem or
/// example, `depends` are the definitions it depends on (`package/name`)
/// and `outside` the constants left, which no entry defines.
pub fn export_entry(
  kind : String,
  name : String,
  statement : String,
  uses : Array[String],
  defines : Array[String],
  loc : String,
  depends? : Array[String] = [],
  outside? : Array[String] = [],
) -> Json {
  let (file, line) = match loc.split(":").collect() {
    [file, line, ..] => {
      let mut n = 0
      for c in line {
        guard c is ('0'..='9') else { break }
        n = n * 10 + (c.to_int() - '0'.to_int())
      }
      (file.to_owned(), n)
    }
    _ => ("", 0)
  }
  let strings = (xs : Array[String]) => Json::array(xs.map(Json::string))
  let fields : Map[String, Json] = Map([
    ("kind", Json::string(kind)),
    ("name", Json::string(name)),
    ("statement", Json::string(statement)),
    ("uses", strings(uses)),
    ("defines", strings(defines)),
    ("file", Json::string(file)),
    ("line", Json::number(line.to_double())),
  ])
  if !depends.is_empty() || !outside.is_empty() {
    fields["depends"] = strings(depends)
    fields["outside"] = strings(outside)
  }
  Json::object(fields)
}

///|
/// The entries of package `pkg` as a JSON object, one entry per line
/// so that a snapshot's diff reads entry by entry.
pub fn render_json(pkg : String, items : Array[Json]) -> String {
  "{\"package\": " +
  Json::string(pkg).stringify() +
  ", \"entries\": [\n" +
  items.map(j => j.stringify()).join(",\n") +
  "\n]}\n"
}
