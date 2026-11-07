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
/// "definition" or "example"); others are not listed.
pub fn record(name : String, th : @kernel.Thm, kind? : String = "lemma") -> Unit {
  if thms.contains(name) {
    abort("wasmcert/logic: " + name + " recorded twice")
  }
  thms[name] = th
  // what load() proves is the theory listing; a user's theorems are not
  if in_load.val {
    entries.push((kind, name, Some(th)))
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
pub fn def(name : String, s : String) -> Unit raise {
  let th = @define.define_(tm(s)) catch {
    e => raise Failure("wasmcert/logic: defining " + name + ": " + e.to_string())
  }
  record(name, th, kind="definition")
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
pub fn lemma(name : String, stmt : String, tac : @tactics.Tactic) -> @kernel.Thm raise {
  let tac = if trace.val {
    println("proving " + name)
    @tactics.then_tac(tac, show_goal("left over"))
  } else {
    tac
  }
  let th = @tactics.prove(tm(stmt), tac) catch {
    e => raise Failure("wasmcert/logic: proving " + name + ": " + e.to_string())
  }
  record(name, th)
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
pub let w8 : String = "Word[Tybit0[Tybit0[Tybit0[Unit]]]]"

///|
/// The type of 32-bit words, as the term syntax writes it.
pub let w32 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]"

///|
/// The type of 64-bit words, as the term syntax writes it.
pub let w64 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]]"

///|
/// A heap: what each address holds, NONE outside it.
pub let heap : String = "(Num) -> Option[\{w8}]"

///|
/// A heap assertion.
pub let hprop : String = "(\{heap}) -> Bool"

///|
/// WasmCert's memories: a limit and the bytes.
let mem_ty : String = "(Limit_t, List[\{w8}])"
