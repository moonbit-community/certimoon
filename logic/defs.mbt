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
fn record(name : String, th : @kernel.Thm, kind? : String = "lemma") -> Unit {
  if thms.contains(name) {
    abort("wasmcert/logic: " + name + " recorded twice")
  }
  thms[name] = th
  entries.push((kind, name, Some(th)))
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
  record(name, th, kind="definition")
}

///|
/// Debugging: when set, `lemma` names each lemma and prints the goals its
/// tactic leaves, and `show_goal` prints. See PLAN.md, "Debugging a proof".
let trace : Ref[Bool] = Ref::{ val: false }

///|
/// A lemma proved by `tac`, recorded as `name`.
fn lemma(name : String, stmt : String, tac : @tactics.Tactic) -> @kernel.Thm raise {
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
/// The type of 64-bit words, as the term syntax writes it.
let w64 : String = "Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]]"

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
/// `tac`, failing unless it proves the goal: for `@tactics.first`, which
/// otherwise takes the first alternative that merely does not fail.
fn solve(tac : @tactics.Tactic) -> @tactics.Tactic {
  @tactics.then_tac(tac, @tactics.no_tac)
}

///|
/// `t` as a new assumption, proved by `proof`.
fn have(t : String, proof : @tactics.Tactic) -> @tactics.Tactic raise {
  @tactics.thenl(
    @tactics.subgoal_then(tm(t), th => @tactics.assume_tac(th)),
    @list.List([proof, @tactics.all_tac]),
  )
}

///|
/// The linear arithmetic fact `t`.
fn arith(t : String) -> @kernel.Thm raise {
  @int.arith_rule(tm(t))
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

///|
/// `mp_tac` of `lemma` (∀ xs. A && B → C) applied to the first two
/// assumptions that match A and B.
fn forward2(lemma : @kernel.Thm) -> @tactics.Tactic {
  g => {
    let asms = g.0.to_array()
    for a in asms {
      for b in asms {
        let th : @kernel.Thm? = Some(@drule.match_mp(lemma)(@bool.conj(a.1, b.1))) catch {
          _ => None
        }
        if th is Some(th) {
          return @tactics.mp_tac(th)(g)
        }
      }
    }
    raise Failure("forward2: no assumptions match")
  }
}

///|
/// step_cases(s, f, code) without computing (`@wasm.step_cases`), kept
/// for the next rule about the same code: it is the slow part of a rule.
let step_cases_seen : Map[String, @kernel.Thm] = Map([])

///|
fn step_cases_of(s : @kernel.Term, f : @kernel.Term, code : String) -> @kernel.Thm raise {
  let key = show(s) + "|" + show(f) + "|" + code
  match step_cases_seen.get(key) {
    Some(th) => th
    None => {
      let th = @wasm.step_cases(s, f, tm(code), compute=false)
      step_cases_seen[key] = th
      th
    }
  }
}
