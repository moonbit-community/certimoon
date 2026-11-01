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
fn record(name : String, th : @kernel.Thm) -> Unit {
  if thms.contains(name) {
    abort("wasmcert/logic: " + name + " recorded twice")
  }
  thms[name] = th
}

///|
fn tm(s : String) -> @kernel.Term raise {
  @term_syntax.parse_term(s)
}

///|
/// A definition by equations, recorded as `name`.
fn def(name : String, s : String) -> Unit raise {
  let th = @define.define_(tm(s)) catch {
    e => raise Failure("wasmcert/logic: defining " + name + ": " + e.to_string())
  }
  record(name, th)
}

///|
let trace : Ref[Bool] = Ref::{ val: false }

///|
/// A lemma proved by `tac`, recorded as `name`.
fn lemma(name : String, stmt : String, tac : @tactics.Tactic) -> @kernel.Thm raise {
  let tac = if trace.val {
    println("proving " + name)
    @tactics.then_tac(tac, g => {
      for a in g.0 {
        println("  [" + a.0 + "] " + show(@kernel.concl(a.1)))
      }
      println("  ⊢ " + show(g.1))
      @tactics.all_tac(g)
    })
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
fn show(t : @kernel.Term) -> String {
  @term_syntax.print_term(t) catch {
    _ => (try @printer.string_of_term(t) catch { _ => "?" })
  }
}

///|
fn seq(tacs : Array[@tactics.Tactic]) -> @tactics.Tactic {
  @tactics.every(@list.List(tacs))
}

///|
fn ths(xs : Array[@kernel.Thm]) -> @list.List[@kernel.Thm] {
  @list.List(xs)
}

///|
/// Word types in the term syntax, as in package wasm.
let w8 : String = "Word[Tybit0[Tybit0[Tybit0[Unit]]]]"

///|
let w32 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]"

///|
/// A heap: what each address holds, NONE outside it.
let heap : String = "(Num) -> Option[\{w8}]"

///|
/// A heap assertion.
let hprop : String = "(\{heap}) -> Bool"

///|
/// WasmCert's memories: a limit and the bytes.
let mem_ty : String = "(Limit_t, List[\{w8}])"

///|
/// Substitutes the assumptions `x == t` (x a variable) everywhere.
fn subst_vars() -> @tactics.Tactic {
  @tactics.repeat_tac(@tactics.first_x_assum(@tactics.subst_var_tac))
}

///|
/// Prints the goal (when tracing), for debugging proofs.
fn show_goal(label : String) -> @tactics.Tactic {
  g => {
    if trace.val {
      println("goal at " + label + ":")
      for a in g.0 {
        println("  [" + a.0 + "] " + show(@kernel.concl(a.1)))
      }
      println("  ⊢ " + show(g.1))
    }
    @tactics.all_tac(g)
  }
}
