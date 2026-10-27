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
  if thms.get(name) is None && !props_loaded.val {
    // the facts about reduction are proved on first use
    props() catch {
      e => abort("wasmcert/wasm: " + e.to_string())
    }
  }
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
  def_thms.push(th)
}

///|
/// Every definition made by `def`, in order: the evaluator computes with
/// them.
let def_thms : Array[@kernel.Thm] = []

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
/// A datatype: HOL type `name` with constructors `(ctor, argument types)`,
/// the types in the term syntax. The type refers to itself by its
/// capitalised name (`List[B_e]` in `b_e`). Recorded as `name_induct` and
/// `name_recursion`.
fn datatype(name : String, ctors : Array[(String, Array[String])]) -> Unit raise {
  let fail = (msg : String) => Failure(
    "wasmcert/wasm: datatype " + name + ": " + msg,
  )
  // An unknown type name reads as a type variable: the only one allowed is
  // the type itself, which HOL's specification syntax writes as `name`.
  let self = name.to_array()[0].to_string().to_upper() +
    String::from_array(name.to_array()[1:])
  let rename = @list.List([
    (@kernel.mk_vartype(name), @kernel.mk_vartype(self)),
  ])
  let alts = []
  for c in ctors {
    let mut alt = c.0
    for s in c.1 {
      let t = ty(s) catch { e => raise fail(c.0 + ": " + e.to_string()) }
      for v in @kernel.tyvars(t) {
        if !(v is Tyvar(n) && n == self) {
          raise fail(c.0 + ": unknown type in " + s)
        }
      }
      alt += " (" + @printer.string_of_type(@kernel.type_subst(rename, t)) + ")"
    }
    alts.push(alt)
  }
  // HOL's define_type reads a specification in its own syntax
  let spec = name + " = " + alts.join(" | ")
  let (induct, recursion) = @ind_types.define_type(spec) catch {
    e => raise fail(e.to_string())
  }
  record(name + "_induct", induct)
  record(name + "_recursion", recursion)
}

///|
/// A datatype whose constructors take no arguments.
fn enum_type(name : String, ctors : Array[String]) -> Unit raise {
  datatype(name, ctors.map(c => (c, [])))
}

///|
/// An uninterpreted constant (Isabelle's `consts` / class parameters),
/// with its type in the term syntax.
fn constant(name : String, t : String) -> Unit raise {
  @kernel.new_constant(name, ty(t))
}

///|
/// An Isabelle record as a one-constructor datatype: `ctor` takes the
/// fields (with types in the term syntax) in order; each field gets an
/// accessor `field(r)` and an update
/// `field_update(x, r)` (Isabelle's `r⦇field := x⦈`).
fn record_type(
  name : String,
  ctor : String,
  fields : Array[(String, String)],
) -> Unit raise {
  datatype(name, [(ctor, fields.map(f => f.1))])
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
