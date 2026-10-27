// Shared plumbing for the WasmCert port: every definition is recorded under
// a name, read back with `thm`.

///|
let thms : Map[String, @kernel.Thm] = Map([])

///|
/// Word types in the term syntax (numeral types are written in binary:
/// `Tybit0[Unit]` is 2).
let w8 : String = "Word[Tybit0[Tybit0[Tybit0[Unit]]]]"

///|
let w32 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]"

///|
let w64 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]]"

///|
let w128 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]]]"

///|
/// Isabelle's `bytes`.
let bytes : String = "List[\{w8}]"

///|
/// Isabelle's `mem` (a memory type and its contents).
let mem_ty : String = "(Limit_t, \{bytes})"

///|
/// Isabelle's `tabinst`.
let tabinst_ty : String = "(Tab_t, List[V_ref])"

///|
/// Isabelle's `eleminst`.
let eleminst_ty : String = "(T_ref, List[V_ref])"

///|
/// A theorem the port made, by name: a definition (`typeof_num`), a
/// datatype's `<type>_induct` / `<type>_recursion`, or an inductive
/// relation's `<rel>_rules` / `<rel>_induct` / `<rel>_cases`.
pub fn thm(name : String) -> @kernel.Thm {
  load()
  match thms.get(name) {
    Some(th) => th
    None => abort("wasmcert/wasm: no theorem " + name)
  }
}

///|
/// The names `thm` knows, in no particular order.
pub fn names() -> Array[String] {
  load()
  thms.keys().collect()
}

///|
fn record(name : String, th : @kernel.Thm) -> Unit {
  if thms.contains(name) {
    abort("wasmcert/wasm: " + name + " recorded twice")
  }
  thms[name] = th
}

///|
fn tm(s : String) -> @kernel.Term raise {
  @term_syntax.parse_term(s)
}

///|
fn ty(s : String) -> @kernel.HolType raise {
  @term_syntax.parse_type(s)
}

///|
/// A definition by equations (`define`), recorded as `name`.
fn def(name : String, s : String) -> Unit raise {
  let th = @define.define_(tm(s)) catch {
    e => raise Failure("wasmcert/wasm: defining " + name + ": " + e.to_string())
  }
  record(name, th)
}

///|
/// Inductive relations `rels` (name, type in the term syntax), one rule
/// per string, recorded as `name_rules`, `name_induct` and `name_cases`.
/// As in Isabelle, each rule is quantified over its own free variables
/// (HOL would read a variable free in the rules as a fixed parameter), and
/// a name may have different types in different rules.
fn inductive(
  name : String,
  rels : Array[(String, String)],
  rules : Array[String],
) -> Unit raise {
  let binders = rels.map(r => "(\{r.0} : \{r.1}) => ").join("")
  let clauses = []
  for i, r in rules {
    let parsed = tm(binders + "(" + r + ")") catch {
      e =>
        raise Failure(
          "wasmcert/wasm: " + name + " rule " + i.to_string() + ": " + e.to_string(),
        )
    }
    let (relvars, body) = @basics.strip_abs(parsed)
    let fvs = @kernel.frees(body).filter(v => !relvars.iter().any(w => w == v))
    clauses.push(@bool.list_mk_forall(fvs, body))
  }
  let spec = @bool.list_mk_conj(@list.List(clauses))
  let (rules, induct, cases) = @ind_defs.new_inductive_definition(spec) catch {
    e => raise Failure("wasmcert/wasm: defining " + name + ": " + e.to_string())
  }
  record(name + "_rules", rules)
  record(name + "_induct", induct)
  record(name + "_cases", cases)
}

///|
/// A datatype from HOL's `define_type` specification (the one place the
/// port writes HOL's own type syntax), recorded as `name_induct` and
/// `name_recursion`.
fn datatype(name : String, spec : String) -> Unit raise {
  let (induct, recursion) = @ind_types.define_type(spec) catch {
    e => raise Failure("wasmcert/wasm: datatype " + name + ": " + e.to_string())
  }
  record(name + "_induct", induct)
  record(name + "_recursion", recursion)
}

///|
/// An uninterpreted constant (Isabelle's `consts` / class parameters),
/// with its type in the term syntax.
fn constant(name : String, t : String) -> Unit raise {
  @kernel.new_constant(name, ty(t))
}

///|
/// An Isabelle record as a one-constructor datatype: `ctor` takes the
/// fields in order; each field gets an accessor `field(r)` and an update
/// `field_update(x, r)` (Isabelle's `r⦇field := x⦈`).
fn record_type(
  name : String,
  ctor : String,
  fields : Array[(String, String)],
) -> Unit raise {
  let spec = name + " = " + ctor + " " + fields.map(f => "(" + f.1 + ")").join(" ")
  datatype(name, spec)
  let vars = Array::makei(fields.length(), i => "x" + (i + 1).to_string())
  let whole = ctor + "(" + vars.join(", ") + ")"
  for i, f in fields {
    def(f.0, "\{f.0}(\{whole}) == \{vars[i]}")
    let updated = vars.mapi((j, v) => if j == i { "v" } else { v })
    def(
      f.0 + "_update",
      "\{f.0}_update(v, \{whole}) == \{ctor}(\{updated.join(", ")})",
    )
  }
}
