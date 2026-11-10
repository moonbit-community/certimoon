// The integer assertions of the spec testsuite (spec_cases_test.mbt): each
// result is a theorem of the semantics, so they check the port's numeric
// layer and reduction rules against the reference results: the control
// flow cases check blocks, loops, branches, frames and calls.

///|
/// A module of the control-flow files, written out for `@wasm.store`: its
/// functions, the block types after the functions' types, its globals and
/// the bytes of its memory (zeros), if it has one.
struct SpecModule {
  funcs : Array[@wasm.Func]
  types : Array[(Array[@wasm.NumType], Array[@wasm.NumType])]
  globals : Array[@wasm.Value]
  memory : Int?
}

///|
test "the spec testsuite's integer assertions hold" {
  let failures = []
  for c in spec_cases {
    let (name, body, expected) = c
    let cfg = @wasm.config(body)
    let want = match expected {
      Some(v) => @wasm.computes_stmt(cfg, [v])
      None => @wasm.traps_stmt(cfg)
    }
    let got = @wasm.outcome(cfg) catch {
      e => {
        failures.push(name + ": " + e.to_string())
        continue
      }
    }
    if !@kernel.hyp(got).is_empty() || !@basics.aconv(@kernel.concl(got), want) {
      failures.push(name + ": got " + @term_syntax.print_term(@kernel.concl(got)))
    }
  }
  if !failures.is_empty() {
    fail("\{failures.length()} of \{spec_cases.length()} cases fail:\n" + failures.join("\n"))
  }
}

///|
test "the spec testsuite's loads at address 0 hold" {
  // address.wast's data, then zeros as far as the loads reach
  let bytes = Array::makei(40, i => if i < 26 { (b'a'.to_int() + i).to_byte() } else { b'\x00' })
  let st = @wasm.store(memory=bytes)
  let failures = []
  for c in spec_load_cases {
    let (name, body, expected) = c
    let cfg = @wasm.config(body, store=st.0, inst=st.1)
    let got = @wasm.outcome(cfg) catch {
      e => {
        failures.push(name + ": " + e.to_string())
        continue
      }
    }
    // computes(cfg, s, vs): loads leave the store as it is
    let want = @wasm.computes_stmt(cfg, [expected.unwrap()])
    if !@kernel.hyp(got).is_empty() || !@basics.aconv(@kernel.concl(got), want) {
      failures.push(name + ": got " + @term_syntax.print_term(@kernel.concl(got)))
    }
  }
  if !failures.is_empty() {
    fail("\{failures.length()} of \{spec_load_cases.length()} cases fail:\n" + failures.join("\n"))
  }
}

///|
/// The functions `code` calls, directly.
fn calls_in(code : Array[@wasm.Instr], out : Array[Int]) -> Unit {
  for ins in code {
    match ins {
      Call(j) => if !out.contains(j) { out.push(j) }
      Block(_, b) | Loop(_, b) => calls_in(b, out)
      If(_, a, b) => {
        calls_in(a, out)
        calls_in(b, out)
      }
      _ => ()
    }
  }
}

///|
/// The functions of `m` that a call of function `j` can reach, `j` first.
fn reachable(m : SpecModule, j : Int) -> Array[Int] {
  let seen = [j]
  let mut i = 0
  while i < seen.length() {
    calls_in(m.funcs[seen[i]].body, seen)
    i += 1
  }
  seen
}

///|
/// `code` with function `used[i]` renumbered i, and the block types (after
/// the module's n functions' types) after the `used.length()` ones.
fn renumber(
  code : Array[@wasm.Instr],
  used : Array[Int],
  n : Int,
) -> Array[@wasm.Instr] {
  let bt = (t : @wasm.BlockType) => match t {
    TypeIndex(i) => @wasm.BlockType::TypeIndex(i - n + used.length())
    t => t
  }
  code.map(ins => match ins {
    Call(j) => @wasm.Instr::Call(used.search(j).unwrap())
    Block(t, b) => Block(bt(t), renumber(b, used, n))
    Loop(t, b) => Loop(bt(t), renumber(b, used, n))
    If(t, a, b) => If(bt(t), renumber(a, used, n), renumber(b, used, n))
    ins => ins
  })
}

///|
/// Runs the control-flow cases, the slow ones too if `slow`, and fails
/// with the ones whose theorem is not the expected one. A module's
/// assertions run in order, each in the memory and globals the one before
/// left (as the file runs them). Each runs in a store of only the
/// functions its call can reach, renumbered from 0 (calls and block types
/// to match): the evaluator's steps cost more with each function of the
/// store, used or not.
fn check_call_cases(slow~ : Bool) -> Unit raise {
  let state : Map[Int, (@kernel.Term, @kernel.Term)] = Map([])
  let failures = []
  let mut ran = 0
  for c in spec_call_cases {
    let (k, name, j, args, expected, is_slow) = c
    if is_slow && !slow {
      continue
    }
    ran += 1
    let m = spec_modules[k]
    let used = reachable(m, j)
    let n = m.funcs.length()
    let funcs = used.map(i => { ..m.funcs[i], body: renumber(m.funcs[i].body, used, n) })
    let memory = m.memory.map(n => Array::make(n, b'\x00'))
    let (s0, inst) = @wasm.store(funcs~, types=m.types, globals=m.globals, memory?)
    // this store's functions, with the memories and globals left before
    let s = match state.get(k) {
      None => s0
      Some((mems, globs)) => {
        let (w, parts) = @basics.strip_comb(s0)
        let parts = parts.to_array()
        parts[2] = mems
        parts[3] = globs
        @basics.list_mk_comb(w, @list.List(parts))
      }
    }
    let body : Array[@wasm.Instr] = args.map(v => match v {
      I32Val(n) => I32Const(n)
      I64Val(n) => I64Const(n)
    })
    body.push(Call(0))
    let cfg = @wasm.config(body, store=s, inst~)
    // fib 20 takes about half a million steps
    let max_steps = if is_slow { 10_000_000 } else { 10_000 }
    let got = @wasm.outcome(cfg, max_steps~) catch {
      e => {
        failures.push(name + ": " + e.to_string())
        continue
      }
    }
    // computes(cfg, s', vs) or traps(cfg, s'), s' the store after the call
    let (f, got_args) = @basics.strip_comb(@kernel.concl(got))
    let got_args = got_args.to_array()
    let after = @basics.strip_comb(got_args[1]).1.to_array()
    state[k] = (after[2], after[3])
    let want = match expected {
      Some(vs) => @wasm.computes_stmt(cfg, vs)
      None => @wasm.traps_stmt(cfg)
    }
    let (g, want_args) = @basics.strip_comb(want)
    let want_args = want_args.to_array()
    let same = @kernel.hyp(got).is_empty() &&
      @basics.aconv(f, g) &&
      got_args.length() == want_args.length() &&
      @basics.aconv(got_args[0], cfg) &&
      (expected is None || @basics.aconv(got_args[2], want_args[2]))
    if !same {
      let result = if got_args.length() == 3 {
        @term_syntax.print_term(got_args[2]) catch { _ => "?" }
      } else {
        "a trap"
      }
      failures.push(name + ": got " + result)
    }
  }
  if !failures.is_empty() {
    fail("\{failures.length()} of \{ran} cases fail:\n" + failures.join("\n"))
  }
}

///|
test "the spec testsuite's control-flow assertions hold" {
  check_call_cases(slow=false)
}

///|
/// With the deep recursions too (SLOW in tools/spec_cases.py): hours.
#skip("hours: the deep recursions of call.wast")
test "the spec testsuite's control-flow assertions hold, the slow ones too" {
  check_call_cases(slow=true)
}
