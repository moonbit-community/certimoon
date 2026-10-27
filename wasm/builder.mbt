// Programs for the evaluator as MoonBit values: each turns into its HOL
// term through the kernel's constructors, without the term parser. The
// instructions are the ones `run` covers, on integers (the port leaves
// floating-point operations unspecified, so they do not compute).

///|
pub(all) enum NumType {
  I32
  I64
}

///|
pub(all) enum Signedness {
  Signed
  Unsigned
}

///|
pub(all) enum IntUnop {
  Clz
  Ctz
  Popcnt
}

///|
pub(all) enum IntBinop {
  Add
  Sub
  Mul
  Div(Signedness)
  Rem(Signedness)
  And
  Or
  Xor
  Shl
  Shr(Signedness)
  Rotl
  Rotr
}

///|
pub(all) enum IntRelop {
  Equal
  NotEqual
  Less(Signedness)
  Greater(Signedness)
  LessEq(Signedness)
  GreaterEq(Signedness)
}

///|
pub(all) enum RefType {
  FuncRef
  ExternRef
}

///|
/// A block's type: no result, one result, or a type in the instance.
pub(all) enum BlockType {
  NoResult
  Result(NumType)
  TypeIndex(Int)
}

///|
/// A value: an i32 or i64, written as its unsigned bits.
pub(all) enum Value {
  I32Val(UInt)
  I64Val(UInt64)
}

///|
pub(all) enum Instr {
  I32Const(UInt)
  I64Const(UInt64)
  Unop(NumType, IntUnop)
  Binop(NumType, IntBinop)
  Eqz(NumType)
  Relop(NumType, IntRelop)
  I32WrapI64
  I64ExtendI32(Signedness)
  RefNull(RefType)
  RefIsNull
  Unreachable
  Nop
  Drop
  Select
  Block(BlockType, Array[Instr])
  Loop(BlockType, Array[Instr])
  If(BlockType, Array[Instr], Array[Instr])
  Br(Int)
  BrIf(Int)
  BrTable(Array[Int], Int)
  LocalGet(Int)
  LocalSet(Int)
  LocalTee(Int)
}

// Kernel term construction, shared with the evaluator.

///|
/// The constant `name` at its declared type (for monomorphic constants).
fn con(name : String) -> @kernel.Term raise {
  @kernel.mk_const(name, @list.List([]))
}

///|
/// The type `name` with no arguments (HOL's name: `einstr`, `wstore`).
fn hol_type(name : String) -> @kernel.HolType raise {
  @kernel.mk_type(name, @list.List([]))
}

///|
/// `name(args...)` for a monomorphic constant `name`.
fn call(name : String, args : Array[@kernel.Term]) -> @kernel.Term raise {
  let mut t = con(name)
  for a in args {
    t = @kernel.mk_comb(t, a)
  }
  t
}

///|
fn num_term(n : String) -> @kernel.Term raise {
  @nums.mk_numeral(@num.num_of_string(n))
}

///|
fn small_num(n : Int) -> @kernel.Term raise {
  @nums.mk_small_numeral(n.to_int64())
}

///|
/// `word(n)` with `bits` bits.
fn word_term(bits : Int, n : String) -> @kernel.Term raise {
  let w = @words.mk_word_ty(@num.num_of_int(bits))
  let word = @basics.mk_mconst("word", @basics.mk_fun_ty(hol_type("num"), w))
  @kernel.mk_comb(word, num_term(n))
}

///|
fn list_term(
  items : Array[@kernel.Term],
  elem : @kernel.HolType,
) -> @kernel.Term raise {
  @lists.mk_list(@list.List(items), elem)
}

///|
fn some_term(t : @kernel.Term) -> @kernel.Term raise {
  @basics.mk_icomb(con("SOME"), t)
}

///|
fn none_term(elem : @kernel.HolType) -> @kernel.Term raise {
  @basics.mk_mconst("NONE", @kernel.mk_type("option", @list.List([elem])))
}

// From the builder's types to terms.

///|
fn NumType::term(self : NumType) -> @kernel.Term raise {
  match self {
    I32 => con("T_i32")
    I64 => con("T_i64")
  }
}

///|
fn Signedness::term(self : Signedness) -> @kernel.Term raise {
  match self {
    Signed => con("S")
    Unsigned => con("U")
  }
}

///|
fn IntUnop::term(self : IntUnop) -> @kernel.Term raise {
  let op = match self {
    Clz => "Clz"
    Ctz => "Ctz"
    Popcnt => "Popcnt"
  }
  call("Unop_i", [con(op)])
}

///|
fn IntBinop::term(self : IntBinop) -> @kernel.Term raise {
  let op = match self {
    Add => con("Add")
    Sub => con("Sub")
    Mul => con("Mul")
    Div(sx) => call("Div", [sx.term()])
    Rem(sx) => call("Rem", [sx.term()])
    And => con("And")
    Or => con("Or")
    Xor => con("Xor")
    Shl => con("Shl")
    Shr(sx) => call("Shr", [sx.term()])
    Rotl => con("Rotl")
    Rotr => con("Rotr")
  }
  call("Binop_i", [op])
}

///|
fn IntRelop::term(self : IntRelop) -> @kernel.Term raise {
  let op = match self {
    Equal => con("Eq")
    NotEqual => con("Ne")
    Less(sx) => call("Lt", [sx.term()])
    Greater(sx) => call("Gt", [sx.term()])
    LessEq(sx) => call("Le", [sx.term()])
    GreaterEq(sx) => call("Ge", [sx.term()])
  }
  call("Relop_i", [op])
}

///|
fn RefType::term(self : RefType) -> @kernel.Term raise {
  match self {
    FuncRef => con("T_func_ref")
    ExternRef => con("T_ext_ref")
  }
}

///|
fn BlockType::term(self : BlockType) -> @kernel.Term raise {
  match self {
    NoResult => call("Tbv", [none_term(hol_type("valtype"))])
    Result(t) => call("Tbv", [some_term(call("T_num", [t.term()]))])
    TypeIndex(i) => call("Tbf", [small_num(i)])
  }
}

///|
/// The value as a HOL `value`: `V_num(ConstInt32(word(n)))`, ...
pub fn Value::to_term(self : Value) -> @kernel.Term raise {
  load()
  let c = match self {
    I32Val(n) => call("ConstInt32", [word_term(32, n.to_string())])
    I64Val(n) => call("ConstInt64", [word_term(64, n.to_string())])
  }
  call("V_num", [c])
}

///|
fn instrs_term(body : Array[Instr]) -> @kernel.Term raise {
  list_term(body.map(i => i.to_term()), hol_type("b_e"))
}

///|
/// The instruction as a HOL `b_e` (a basic instruction).
pub fn Instr::to_term(self : Instr) -> @kernel.Term raise {
  load()
  match self {
    I32Const(n) =>
      call("EConstNum", [call("ConstInt32", [word_term(32, n.to_string())])])
    I64Const(n) =>
      call("EConstNum", [call("ConstInt64", [word_term(64, n.to_string())])])
    Unop(t, op) => call("Unop", [t.term(), op.term()])
    Binop(t, op) => call("Binop", [t.term(), op.term()])
    Eqz(t) => call("Testop", [t.term(), con("Eqz")])
    Relop(t, op) => call("Relop", [t.term(), op.term()])
    I32WrapI64 =>
      call("Cvtop", [
        con("T_i32"),
        con("Convert"),
        con("T_i64"),
        none_term(sat_sx_type()),
      ])
    I64ExtendI32(sx) =>
      call("Cvtop", [
        con("T_i64"),
        con("Convert"),
        con("T_i32"),
        some_term(@pair.mk_pair((con("Nonsat"), sx.term()))),
      ])
    RefNull(t) => call("Ref_null", [t.term()])
    RefIsNull => con("Ref_is_null")
    Unreachable => con("Unreachable")
    Nop => con("Nop")
    Drop => con("Drop")
    Select => call("Select", [none_term(hol_type("valtype"))])
    Block(bt, body) => call("Block", [bt.term(), instrs_term(body)])
    Loop(bt, body) => call("Loop", [bt.term(), instrs_term(body)])
    If(bt, then_, else_) =>
      call("If", [bt.term(), instrs_term(then_), instrs_term(else_)])
    Br(i) => call("Br", [small_num(i)])
    BrIf(i) => call("Br_if", [small_num(i)])
    BrTable(is_, i) =>
      call("Br_table", [list_term(is_.map(small_num), hol_type("num")), small_num(i)])
    LocalGet(i) => call("Local_get", [small_num(i)])
    LocalSet(i) => call("Local_set", [small_num(i)])
    LocalTee(i) => call("Local_tee", [small_num(i)])
  }
}

///|
/// `(Sat, Sx)`.
fn sat_sx_type() -> @kernel.HolType raise {
  @kernel.mk_type("prod", @list.List([hol_type("sat"), hol_type("sx")]))
}

///|
/// The configuration `(s, Wframe(locals, i), body)` that runs `body`:
/// in `store` and instance `inst`, by default the variables `s : Wstore`
/// and `i : Inst` (so a result about it holds for every store and
/// instance).
pub fn config(
  body : Array[Instr],
  locals? : Array[Value] = [],
  store? : @kernel.Term,
  inst? : @kernel.Term,
) -> @kernel.Term raise {
  load()
  let s = match store {
    Some(t) => t
    None => @kernel.mk_var("s", hol_type("wstore"))
  }
  let i = match inst {
    Some(t) => t
    None => @kernel.mk_var("i", hol_type("inst"))
  }
  let frame = call("Wframe", [
    list_term(locals.map(v => v.to_term()), hol_type("value")),
    i,
  ])
  let es = list_term(body.map(b => call("Basic", [b.to_term()])), hol_type("einstr"))
  @pair.mk_pair((s, @pair.mk_pair((frame, es))))
}

///|
/// `computes(cfg, s, vs)`: `cfg` runs to the values `results` (in stack
/// order, the top last) in its own store `s` (which the instructions
/// `run` covers do not change).
pub fn computes_stmt(
  cfg : @kernel.Term,
  results : Array[Value],
) -> @kernel.Term raise {
  let vs = results.map(v => v.to_term())
  // computes lists the value stack top first
  vs.rev_in_place()
  let (s, _) = @pair.dest_pair(cfg)
  call("computes", [cfg, s, list_term(vs, hol_type("value"))])
}

///|
/// `traps(cfg, s)`, `s` the store of `cfg`.
pub fn traps_stmt(cfg : @kernel.Term) -> @kernel.Term raise {
  let (s, _) = @pair.dest_pair(cfg)
  call("traps", [cfg, s])
}
