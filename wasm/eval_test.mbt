// The evaluator on small programs written with the builder: each result
// is a theorem.

///|
/// Checks that `body`'s outcome is `expected(cfg)`, with no hypotheses.
fn check(
  body : Array[@wasm.Instr],
  locals : Array[@wasm.Value],
  expected : (@kernel.Term) -> @kernel.Term raise,
) -> Unit raise {
  let cfg = @wasm.config(body, locals~)
  let th = @wasm.outcome(cfg)
  assert_true(@kernel.hyp(th).is_empty())
  if !@basics.aconv(@kernel.concl(th), expected(cfg)) {
    fail("got " + @term_syntax.print_term(@kernel.concl(th)))
  }
}

///|
fn computes(
  body : Array[@wasm.Instr],
  result : @wasm.Value,
  locals? : Array[@wasm.Value] = [],
) -> Unit raise {
  check(body, locals, cfg => @wasm.computes_stmt(cfg, [result]))
}

///|
fn traps(body : Array[@wasm.Instr]) -> Unit raise {
  check(body, [], @wasm.traps_stmt)
}

///|
/// The message `run` raises on `cfg`.
fn run_error(cfg : @kernel.Term) -> String {
  try {
    ignore(@wasm.run(cfg))
    "no error"
  } catch {
    Failure(m) => m
    e => e.to_string()
  }
}

///|
test "the builder writes the terms of the term syntax" {
  let cases : Array[(@wasm.Instr, String)] = [
    (I32Const(10), "EConstNum(ConstInt32(word(10)))"),
    (I64Const(0xFFFF_FFFF_FFFF_FFFF), "EConstNum(ConstInt64(word(18446744073709551615)))"),
    (Unop(I32, Popcnt), "Unop(T_i32, Unop_i(Popcnt))"),
    (Binop(I64, Shr(Unsigned)), "Binop(T_i64, Binop_i(Shr(U)))"),
    (Eqz(I64), "Testop(T_i64, Eqz)"),
    (Relop(I32, GreaterEq(Signed)), "Relop(T_i32, Relop_i(Ge(S)))"),
    (I32WrapI64, "Cvtop(T_i32, Convert, T_i64, NONE)"),
    (I64ExtendI32(Unsigned), "Cvtop(T_i64, Convert, T_i32, SOME((Nonsat, U)))"),
    (ExtendS(I64, P32), "Unop(T_i64, Extend_s(Tp_i32))"),
    (RefNull(ExternRef), "Ref_null(T_ext_ref)"),
    (Select, "Select(NONE)"),
    (Block(Result(I32), [Nop]), "Block(Tbv(SOME(T_num(T_i32))), [Nop])"),
    (Loop(NoResult, []), "Loop(Tbv(NONE), NIL)"),
    (If(TypeIndex(2), [Drop], [Unreachable]), "If(Tbf(2), [Drop], [Unreachable])"),
    (BrTable([0, 1], 2), "Br_table([0, 1], 2)"),
    (LocalTee(3), "Local_tee(3)"),
  ]
  for c in cases {
    let (instr, text) = c
    assert_true(
      @basics.aconv(instr.to_term(), @term_syntax.parse_term(text)),
      msg=text,
    )
  }
  assert_true(
    @basics.aconv(
      @wasm.config([Nop], locals=[I32Val(1)]),
      @term_syntax.parse_term(
        "((s : Wstore), Wframe([V_num(ConstInt32(word(1)))], (i : Inst)), [Basic(Nop)])",
      ),
    ),
  )
}

///|
test "straight-line code computes" {
  // 10 / 2 + 3
  computes(
    [I32Const(10), I32Const(2), Binop(I32, Div(Signed)), I32Const(3), Binop(I32, Add)],
    I32Val(8),
  )
  // (3 < 4) == 0
  computes([I32Const(3), I32Const(4), Relop(I32, Less(Signed)), Eqz(I32)], I32Val(0))
  // select picks its second value when the condition is 0; drop
  computes([I32Const(1), I32Const(2), I32Const(0), Select, I32Const(4), Drop], I32Val(2))
  // count trailing zeros
  computes([I32Const(8), Unop(I32, Ctz)], I32Val(3))
  // conversions: wrap keeps the low 32 bits, a signed extend copies the sign
  computes([I64Const(0x1_0000_0005), I32WrapI64], I32Val(5))
  computes([I32Const(0xFFFF_FFFF), I64ExtendI32(Signed)], I64Val(0xFFFF_FFFF_FFFF_FFFF))
  computes([I32Const(0xFFFF_FFFF), I64ExtendI32(Unsigned)], I64Val(0xFFFF_FFFF))
  // a null reference is null
  computes([RefNull(FuncRef), RefIsNull], I32Val(1))
}

///|
test "division by zero and unreachable trap" {
  traps([I32Const(1), I32Const(0), Binop(I32, Div(Signed))])
  // INT_MIN / -1 overflows
  traps([I32Const(0x8000_0000), I32Const(0xFFFF_FFFF), Binop(I32, Div(Signed))])
  // inside blocks, the trap ends the whole program
  traps([Block(NoResult, [I32Const(1), Block(NoResult, [Unreachable]), Drop]), I32Const(5)])
}

///|
test "blocks and branches" {
  // a block's result
  computes([Block(Result(I32), [I32Const(7)]), I32Const(1), Binop(I32, Add)], I32Val(8))
  // br 1 leaves both blocks, taking the outer block's one value
  computes(
    [Block(Result(I32), [Block(NoResult, [I32Const(5), Br(1)]), I32Const(9)])],
    I32Val(5),
  )
  // br_if 0 leaves the block only when its condition is not 0
  let br_if = (c : UInt) => [
    @wasm.Block(Result(I32), [I32Const(1), I32Const(c), BrIf(0), Drop, I32Const(2)]),
  ]
  computes(br_if(1), I32Val(1))
  computes(br_if(0), I32Val(2))
  // if
  let choose = (c : UInt) => [
    @wasm.I32Const(c),
    If(Result(I32), [I32Const(10)], [I32Const(20)]),
  ]
  computes(choose(3), I32Val(10))
  computes(choose(0), I32Val(20))
  // br_table: index 0 leaves the inner block (dropping 30); an index out
  // of range takes the default, 1, and leaves with 30
  let table = (c : UInt) => [
    @wasm.Block(Result(I32), [
      Block(NoResult, [I32Const(30), I32Const(c), BrTable([0], 1)]),
      I32Const(20),
    ]),
  ]
  computes(table(0), I32Val(20))
  computes(table(5), I32Val(30))
}

///|
test "a loop over locals" {
  // n = 5, acc = 0; loop { acc += n; n -= 1; br_if 0 (n) }; acc
  let body : Array[@wasm.Instr] = [
    LocalGet(1),
    LocalGet(0),
    Binop(I32, Add),
    LocalSet(1),
    LocalGet(0),
    I32Const(1),
    Binop(I32, Sub),
    LocalTee(0),
    BrIf(0),
  ]
  computes([Loop(NoResult, body), LocalGet(1)], I32Val(15), locals=[I32Val(5), I32Val(0)])
}

///|
/// Checks that `body` computes `result` in the store `store` (with its
/// instance), with no hypotheses.
fn computes_in(
  st : (@kernel.Term, @kernel.Term),
  body : Array[@wasm.Instr],
  result : Array[@wasm.Value],
  locals? : Array[@wasm.Value] = [],
) -> @kernel.Thm raise {
  let cfg = @wasm.config(body, locals~, store=st.0, inst=st.1)
  let th = @wasm.outcome(cfg)
  assert_true(@kernel.hyp(th).is_empty())
  // computes(cfg, s', vs): the values, whatever the final store
  let (_, args) = @basics.strip_comb(@kernel.concl(th))
  let want = @kernel.rand(@wasm.computes_stmt(cfg, result))
  if !@basics.aconv(args.to_array()[2], want) {
    fail("got " + @term_syntax.print_term(@kernel.concl(th)))
  }
  th
}

///|
fn traps_in(st : (@kernel.Term, @kernel.Term), body : Array[@wasm.Instr]) -> Unit raise {
  let cfg = @wasm.config(body, store=st.0, inst=st.1)
  let th = @wasm.outcome(cfg)
  assert_true(@kernel.hyp(th).is_empty())
  let head = @basics.strip_comb(@kernel.concl(th)).0
  assert_true(@kernel.dest_const(head).0 == "traps")
}

///|
test "loads and stores" {
  let st = @wasm.store(memory=[b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', b'\x06', b'\x07', b'\x08'])
  // little endian: bytes 1..4 at address 0
  computes_in(st, [I32Const(0), Load(I32, 0)], [I32Val(0x04030201)]) |> ignore
  // the offset adds to the address
  computes_in(st, [I32Const(1), Load(I32, 3)], [I32Val(0x08070605)]) |> ignore
  computes_in(st, [I32Const(0), Load(I64, 0)], [I64Val(0x0807060504030201)]) |> ignore
  // packed loads extend
  computes_in(st, [I32Const(7), LoadPacked(I32, P8, Unsigned, 0)], [I32Val(8)]) |> ignore
  // a store, then a load of what it wrote
  computes_in(
    st,
    [I32Const(2), I32Const(0xFFFF_FF80), StorePacked(I32, P8, 0), I32Const(2), LoadPacked(I32, P8, Signed, 0)],
    [I32Val(0xFFFF_FF80)],
  )
  |> ignore
  computes_in(
    st,
    [I32Const(4), I32Const(0xDEAD_BEEF), Store(I32, 0), I32Const(0), Load(I64, 0)],
    [I64Val(0xDEAD_BEEF_0403_0201)],
  )
  |> ignore
  // out of bounds: the last byte read would be byte 8
  traps_in(st, [I32Const(5), Load(I32, 0)])
  traps_in(st, [I32Const(0), I64Const(1), Store(I64, 1)])
  // a memory of 8 bytes has 0 pages
  computes_in(st, [MemorySize], [I32Val(0)]) |> ignore
}

///|
test "memory.fill and memory.copy" {
  let st = @wasm.store(memory=[b'\x01', b'\x02', b'\x03', b'\x04', b'\x00', b'\x00', b'\x00', b'\x00'])
  computes_in(
    st,
    [I32Const(4), I32Const(0xAB), I32Const(3), MemoryFill, I32Const(4), Load(I32, 0)],
    [I32Val(0x00AB_ABAB)],
  )
  |> ignore
  // overlapping copy towards higher addresses copies from the top down
  computes_in(
    st,
    [I32Const(1), I32Const(0), I32Const(3), MemoryCopy, I32Const(0), Load(I32, 0)],
    [I32Val(0x0302_0101)],
  )
  |> ignore
  traps_in(st, [I32Const(6), I32Const(0), I32Const(3), MemoryFill])
}

///|
test "globals and calls" {
  // function 0: (x, y) -> x - y; function 1: x -> f0(x, 1) via a local,
  // and it counts its calls in global 0
  let sub : @wasm.Func = {
    params: [I32, I32],
    results: [I32],
    locals: [],
    body: [LocalGet(0), LocalGet(1), Binop(I32, Sub)],
  }
  let dec : @wasm.Func = {
    params: [I32],
    results: [I32],
    locals: [I32],
    body: [
      GlobalGet(0),
      I32Const(1),
      Binop(I32, Add),
      GlobalSet(0),
      I32Const(1),
      LocalSet(1),
      LocalGet(0),
      LocalGet(1),
      Call(0),
      Return,
      Unreachable,
    ],
  }
  let st = @wasm.store(funcs=[sub, dec], globals=[I32Val(10)])
  computes_in(st, [I32Const(7), I32Const(2), Call(0)], [I32Val(5)]) |> ignore
  computes_in(st, [I32Const(7), Call(1), Call(1), GlobalGet(0)], [I32Val(5), I32Val(12)])
  |> ignore
}

///|
test "what the evaluator cannot run" {
  // memory needs the store written out
  let load = run_error(
    @term_syntax.parse_term(
      "((s : Wstore), Wframe(NIL, (i : Inst)), [Basic(EConstNum(ConstInt32(word(0)))), Basic(Load(T_i32, NONE, 0, 0))])",
    ),
  )
  assert_true(load.contains("no memory"), msg=load)
  // a br outside every block
  let br = run_error(@wasm.config([Br(0)]))
  assert_true(br.contains("a br leaves every block"), msg=br)
  // a missing operand
  let add = run_error(@wasm.config([I32Const(1), Binop(I32, Add)]))
  assert_true(add.contains("Binop needs 2 values and has 1"), msg=add)
}

///|
test "indirect calls" {
  // function 0: x -> x + x; function 1: (x, y) -> x - y; the table holds
  // function 0 at 0, function 1 at 1 and null at 2
  let double : @wasm.Func = {
    params: [I32],
    results: [I32],
    locals: [],
    body: [LocalGet(0), LocalGet(0), Binop(I32, Add)],
  }
  let sub : @wasm.Func = {
    params: [I32, I32],
    results: [I32],
    locals: [],
    body: [LocalGet(0), LocalGet(1), Binop(I32, Sub)],
  }
  let st = @wasm.store(funcs=[double, sub], tables=[[Some(0), Some(1), None]])
  // type 0 is double's, type 1 sub's
  computes_in(st, [I32Const(21), I32Const(0), CallIndirect(0, 0)], [I32Val(42)])
  |> ignore
  computes_in(st, [I32Const(7), I32Const(2), I32Const(1), CallIndirect(0, 1)], [I32Val(5)])
  |> ignore
  // the wrong type, a null entry, and past the table's end trap
  let (s, i) = st
  for c in [1U, 2, 3] {
    let cfg = @wasm.config([I32Const(5), I32Const(c), CallIndirect(0, 0)], store=s, inst=i)
    let th = @wasm.outcome(cfg)
    assert_true(@kernel.hyp(th).is_empty())
    if !@basics.aconv(@kernel.concl(th), @wasm.traps_stmt(cfg)) {
      fail("got " + @term_syntax.print_term(@kernel.concl(th)))
    }
  }
}
