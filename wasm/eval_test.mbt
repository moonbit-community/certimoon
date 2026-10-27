// The evaluator on small programs: each result is a theorem.

///|
fn i32(n : Int) -> String {
  i32_of(n.to_string())
}

///|
fn i32_of(n : String) -> String {
  "EConstNum(ConstInt32(word(\{n})))"
}

///|
fn binop(op : String) -> String {
  "Binop(T_i32, Binop_i(\{op}))"
}

///|
/// A block type with one i32 result.
let to_i32 : String = "Tbv(SOME(T_num(T_i32)))"

///|
/// A block type with no results.
let to_none : String = "Tbv(NONE)"

///|
/// The configuration running `body` (basic instructions) in a frame with
/// i32 locals `locals`, in any store `s` and instance `i`.
fn config(body : Array[String], locals? : Array[Int] = []) -> String {
  let locs = locals.map(n => "V_num(ConstInt32(word(\{n})))").join(", ")
  let es = body.map(b => "Basic(\{b})").join(", ")
  "((s : Wstore), Wframe(([\{locs}] : List[Value]), (i : Inst)), [\{es}])"
}

///|
/// Checks that the outcome of `cfg` is `expected` (a computes or traps
/// statement about `cfg`) and has no hypotheses.
fn check_outcome(cfg : String, expected : String) -> Unit raise {
  let th = @wasm.outcome(@term_syntax.parse_term(cfg))
  assert_true(@kernel.hyp(th).is_empty())
  let want = @term_syntax.parse_term(expected)
  if !@basics.aconv(@kernel.concl(th), want) {
    fail("got " + @term_syntax.print_term(@kernel.concl(th)))
  }
}

///|
fn computes(cfg : String, n : Int) -> Unit raise {
  check_outcome(cfg, "computes(\{cfg}, s, [V_num(ConstInt32(word(\{n})))])")
}

///|
fn traps(cfg : String) -> Unit raise {
  check_outcome(cfg, "traps(\{cfg}, s)")
}

///|
/// The message `run` raises on `cfg`.
fn run_error(cfg : String) -> String {
  try {
    ignore(@wasm.run(@term_syntax.parse_term(cfg)))
    "no error"
  } catch {
    Failure(m) => m
    e => e.to_string()
  }
}

///|
test "straight-line code computes" {
  // 10 / 2 + 3
  computes(config([i32(10), i32(2), binop("Div(S)"), i32(3), binop("Add")]), 8)
  // (3 < 4) == 0
  computes(
    config([
      i32(3),
      i32(4),
      "Relop(T_i32, Relop_i(Lt(S)))",
      "Testop(T_i32, Eqz)",
    ]),
    0,
  )
  // select picks its second value when the condition is 0; drop
  computes(config([i32(1), i32(2), i32(0), "Select(NONE)", i32(4), "Drop"]), 2)
}

///|
test "division by zero and unreachable trap" {
  traps(config([i32(1), i32(0), binop("Div(S)")]))
  // INT_MIN / -1 overflows (word takes the unsigned value)
  traps(config([i32_of("2147483648"), i32_of("4294967295"), binop("Div(S)")]))
  // inside blocks, the trap ends the whole program
  traps(
    config([
      "Block(\{to_none}, [\{i32(1)}, Block(\{to_none}, [Unreachable]), Drop])",
      i32(5),
    ]),
  )
}

///|
test "blocks and branches" {
  // a block's result
  computes(config(["Block(\{to_i32}, [\{i32(7)}])", i32(1), binop("Add")]), 8)
  // br 1 leaves both blocks, taking the outer block's one value
  computes(
    config([
      "Block(\{to_i32}, [Block(\{to_none}, [\{i32(5)}, Br(1)]), \{i32(9)}])",
    ]),
    5,
  )
  // br_if 0 leaves the block only when its condition is not 0
  let br_if = (c : Int) => config([
    "Block(\{to_i32}, [\{i32(1)}, \{i32(c)}, Br_if(0), Drop, \{i32(2)}])",
  ])
  computes(br_if(1), 1)
  computes(br_if(0), 2)
  // if
  let choose = (c : Int) => config([
    i32(c),
    "If(\{to_i32}, [\{i32(10)}], [\{i32(20)}])",
  ])
  computes(choose(3), 10)
  computes(choose(0), 20)
  // br_table: index 0 leaves the inner block (dropping 30); an index out
  // of range takes the default, 1, and leaves with 30
  let table = (c : Int) => config([
    "Block(\{to_i32}, [Block(\{to_none}, [\{i32(30)}, \{i32(c)}, Br_table([0], 1)]), \{i32(20)}])",
  ])
  computes(table(0), 20)
  computes(table(5), 30)
}

///|
test "a loop over locals" {
  // n = 5, acc = 0; loop { acc += n; n -= 1; br_if 0 (n) }; acc
  let body = [
    "Local_get(1)", "Local_get(0)", binop("Add"), "Local_set(1)", "Local_get(0)",
    i32(1), binop("Sub"), "Local_tee(0)", "Br_if(0)",
  ]
  computes(
    config(["Loop(\{to_none}, [\{body.join(", ")}])", "Local_get(1)"], locals=[
      5, 0,
    ]),
    15,
  )
}

///|
test "what the evaluator cannot run" {
  // memory is not covered
  let load = run_error(config([i32(0), "Load(T_i32, NONE, 0, 0)"]))
  assert_true(load.contains("no rule for Load(T_i32, NONE, 0, 0)"), msg=load)
  // a br outside every block
  let br = run_error(config(["Br(0)"]))
  assert_true(br.contains("a br leaves every block"), msg=br)
  // a missing operand
  let add = run_error(config([i32(1), binop("Add")]))
  assert_true(add.contains("Binop needs 2 values and has 1"), msg=add)
}
