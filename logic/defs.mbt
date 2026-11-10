// Shared plumbing for the program logic: every definition and lemma is
// recorded under a name, read back with `thm` (as in package wasm).

///|
let thms : Map[String, @kernel.Thm] = Map([])

///|
/// A definition or lemma of the logic, by name.
pub fn thm(name : String) -> @kernel.Thm {
  load()
  match thms.get(name) {
    Some(th) => th
    None => abort("wasmcert/logic: no theorem " + name)
  }
}

///|
/// The names `thm` knows, in no particular order.
pub fn names() -> Array[String] {
  load()
  thms.keys().collect()
}

///|
/// Records `th` as `name`, for `thm` (a name can be recorded once). The
/// theorems load() records are the theory listing (kind: "lemma",
/// "definition", "program" (a definition of code, `program`), "example", a triple of a verified program, or "theorem",
/// a closed theorem: about the program's runs, with no assertion or
/// triple); others are not listed.
#callsite(autofill(loc))
pub fn record(
  name : String,
  th : @kernel.Thm,
  kind? : String = "lemma",
  loc~ : SourceLoc,
) -> Unit {
  if thms.contains(name) {
    abort("wasmcert/logic: " + name + " recorded twice")
  }
  thms[name] = th
  // what load() proves is the theory listing; a user's theorems are not
  if in_load.val {
    let defines = @wasm.defined_constants(kind, th)
    entries.push({ kind, name, th: Some(th), defines, loc: loc.to_string() })
  }
}

///|
/// The term `s`, in hol_light's term syntax (as the theory listing prints
/// terms).
pub fn tm(s : String) -> @kernel.Term raise {
  @term_syntax.parse_term(s)
}

///|
/// A definition by equations, recorded as `name`.
#callsite(autofill(loc))
pub fn def(name : String, s : String, loc~ : SourceLoc) -> Unit raise {
  let th = @define.define_(tm(s)) catch {
    e => raise Failure("wasmcert/logic: defining " + name + ": " + e.to_string())
  }
  record(name, th, kind="definition", loc~)
}

///|
/// The programs' definitions (`program`), for unfolding their names.
let programs : Array[@kernel.Thm] = []

///|
/// A program: the constant `name` defined as `code`, a list of basic
/// instructions (`List[B_e]`), recorded as `name` and listed in
/// WebAssembly's text format. Code with free variables (a constant `x` to
/// store, say) takes them as `params`, each with its type (`"(x : W)"`),
/// and defines `name(x, ...)`. Returns `name` (or `name(x, ...)`), so that
/// statements name the code; `sym_prove` and `call_free_tac` unfold it
/// (`program_defs`).
#callsite(autofill(loc))
pub fn program(
  name : String,
  code : String,
  params? : Array[String] = [],
  loc~ : SourceLoc,
) -> String raise {
  let lhs = if params.is_empty() { name } else { name + "(" + params.join(", ") + ")" }
  let th = @define.define_(tm(lhs + " == (" + code + " : List[B_e])")) catch {
    e => raise Failure("wasmcert/logic: defining " + name + ": " + e.to_string())
  }
  programs.push(th)
  record(name, th, kind="program", loc~)
  lhs
}

///|
/// The definition of the program `code` names (`name` or `name(x, ...)`),
/// if it names one.
fn program_def(code : @kernel.Term) -> @kernel.Thm? raise {
  let head = @basics.strip_comb(code).0
  guard @kernel.is_const(head) else { return None }
  for d in programs {
    let lhs = @kernel.dest_eq(@basics.strip_forall(@kernel.concl(d)).1).0
    if @basics.aconv(@basics.strip_comb(lhs).0, head) {
      return Some(d)
    }
  }
  None
}

///|
/// The definitions of the programs made so far (`program`).
pub fn program_defs() -> Array[@kernel.Thm] {
  programs.copy()
}

///|
/// Debugging: when set, `lemma` names each lemma and prints the goals its
/// tactic leaves, and `show_goal` prints. See PLAN.md, "Debugging a proof".
let trace : Ref[Bool] = Ref::{ val: false }

///|
/// Turns tracing on or off (see `trace`): for debugging a proof.
pub fn set_trace(on : Bool) -> Unit {
  trace.val = on
}

///|
/// A lemma proved by `tac`, recorded as `name`.
#callsite(autofill(loc))
pub fn lemma(
  name : String,
  stmt : String,
  tac : @tactics.Tactic,
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  let tac = if trace.val {
    println("proving " + name)
    @tactics.then_tac(tac, show_goal("left over"))
  } else {
    tac
  }
  let th = @tactics.prove(tm(stmt), tac) catch {
    e => raise Failure("wasmcert/logic: proving " + name + ": " + e.to_string())
  }
  record(name, th, loc~)
  th
}

///|
/// `t` in the term syntax (or HOL Light's syntax, if the term syntax
/// cannot print it).
pub fn show(t : @kernel.Term) -> String {
  @term_syntax.print_term(t) catch {
    _ => (try @printer.string_of_term(t) catch { _ => "?" })
  }
}

///|
/// The tactics in order, each on every goal the one before leaves.
pub fn seq(tacs : Array[@tactics.Tactic]) -> @tactics.Tactic {
  @tactics.every(@list.List(tacs))
}

///|
/// A list of theorems, for the rewriting and MESON tactics.
pub fn ths(xs : Array[@kernel.Thm]) -> @list.List[@kernel.Thm] {
  @list.List(xs)
}

///|
/// The type of bytes, as the term syntax writes it (as in package wasm).
pub let w8 : String = "Word[8]"

///|
/// The type of 32-bit words, as the term syntax writes it.
pub let w32 : String = "Word[32]"

///|
/// The type of 64-bit words, as the term syntax writes it.
pub let w64 : String = "Word[64]"

///|
/// A heap: what each address holds, NONE outside it.
pub let heap : String = "(Num) -> Option[\{w8}]"

///|
/// A heap assertion.
pub let hprop : String = "(\{heap}) -> Bool"

///|
/// WasmCert's memories: a limit and the bytes.
let mem_ty : String = "(Limit_t, List[\{w8}])"
