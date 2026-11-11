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
/// The width of a packed load or store.
pub(all) enum PackedType {
  P8
  P16
  P32
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
  // i32.extend8_s, i64.extend32_s, ...: sign-extend the low bits
  ExtendS(NumType, PackedType)
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
  Return
  Call(Int)
  // call_indirect: the table, then the type
  CallIndirect(Int, Int)
  GlobalGet(Int)
  GlobalSet(Int)
  // loads and stores take their offset; the alignment hint is 0
  Load(NumType, Int)
  LoadPacked(NumType, PackedType, Signedness, Int)
  Store(NumType, Int)
  StorePacked(NumType, PackedType, Int)
  MemorySize
  MemoryGrow
  MemoryFill
  MemoryCopy
}

///|
/// A function of the store: its parameter, result and local types and its
/// body.
pub(all) struct Func {
  params : Array[NumType]
  results : Array[NumType]
  locals : Array[NumType]
  body : Array[Instr]
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
    ExtendS(t, tp) => call("Unop", [t.term(), call("Extend_s", [tp.term()])])
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
    Return => con("Return")
    Call(i) => call("Call", [small_num(i)])
    CallIndirect(t, j) => call("Call_indirect", [small_num(t), small_num(j)])
    GlobalGet(i) => call("Global_get", [small_num(i)])
    GlobalSet(i) => call("Global_set", [small_num(i)])
    Load(t, off) =>
      call("Load", [t.term(), none_term(tp_sx_type()), small_num(0), small_num(off)])
    LoadPacked(t, tp, sx, off) =>
      call("Load", [
        t.term(),
        some_term(@pair.mk_pair((tp.term(), sx.term()))),
        small_num(0),
        small_num(off),
      ])
    Store(t, off) =>
      call("Store", [t.term(), none_term(hol_type("tp_num")), small_num(0), small_num(off)])
    StorePacked(t, tp, off) =>
      call("Store", [t.term(), some_term(tp.term()), small_num(0), small_num(off)])
    MemorySize => con("Memory_size")
    MemoryGrow => con("Memory_grow")
    MemoryFill => con("Memory_fill")
    MemoryCopy => con("Memory_copy")
  }
}

///|
fn PackedType::term(self : PackedType) -> @kernel.Term raise {
  match self {
    P8 => con("Tp_i8")
    P16 => con("Tp_i16")
    P32 => con("Tp_i32")
  }
}

///|
/// `(Tp_num, Sx)`.
fn tp_sx_type() -> @kernel.HolType raise {
  @kernel.mk_type("prod", @list.List([hol_type("tp_num"), hol_type("sx")]))
}

///|
/// `[T_num(t), ...]`.
fn valtypes_term(ts : Array[NumType]) -> @kernel.Term raise {
  list_term(ts.map(t => call("T_num", [t.term()])), hol_type("valtype"))
}

///|
/// `[0, 1, ..., n - 1]`.
fn indices_term(n : Int) -> @kernel.Term raise {
  list_term(Array::makei(n, small_num), hol_type("num"))
}

///|
/// A store and its one instance `(s, i)`, written out: the functions
/// `funcs` (function j is index j, and its type is type j of the
/// instance; `types` are the instance's types after those, for blocks:
/// `TypeIndex(funcs.length() + k)` is `types[k]`), a memory with the
/// bytes `memory` (if given; at most `max_pages` pages after growing),
/// mutable globals with the values `globals` and, if `table` is given, a
/// table of function references (an entry is a function's index, or None
/// for a null reference). The memory is not rounded to pages: the
/// evaluator computes on its bytes one by one, so keep it small.
pub fn store(
  funcs? : Array[Func] = [],
  types? : Array[(Array[NumType], Array[NumType])] = [],
  table? : Array[Int?],
  memory? : Array[Byte],
  max_pages? : Int,
  globals? : Array[Value] = [],
) -> (@kernel.Term, @kernel.Term) raise {
  load()
  let num = hol_type("num")
  let tfs = funcs.map(fn(fu) raise {
    call("Tf", [valtypes_term(fu.params), valtypes_term(fu.results)])
  })
  let block_tfs = types.map(fn(t) raise {
    call("Tf", [valtypes_term(t.0), valtypes_term(t.1)])
  })
  let mems = match memory {
    Some(_) => [0]
    None => []
  }
  let tabs = match table {
    Some(_) => [0]
    None => []
  }
  let inst = call("Inst", [
    list_term(tfs + block_tfs, hol_type("tf")),
    indices_term(funcs.length()),
    list_term(tabs.map(small_num), num),
    list_term(mems.map(small_num), num),
    indices_term(globals.length()),
    list_term([], num),
    list_term([], num),
  ])
  let cls = []
  for i, fu in funcs {
    cls.push(
      call("Func_native", [inst, tfs[i], valtypes_term(fu.locals), instrs_term(fu.body)]),
    )
  }
  let mem_items = match memory {
    Some(bytes) => {
      let max = match max_pages {
        Some(p) => some_term(small_num(p))
        None => none_term(num)
      }
      let lim = call("Limit_t", [small_num(bytes.length() / 65536), max])
      let bs = list_term(bytes.map(b => word_term(8, b.to_int().to_string())), ty(w8))
      [@pair.mk_pair((lim, bs))]
    }
    None => []
  }
  let globs = globals.map(v => call("Global", [con("T_mut"), v.to_term()]))
  let tab_items = match table {
    Some(entries) => {
      let refs = entries.map(fn(e) raise {
        match e {
          Some(j) => call("ConstRefFunc", [small_num(j)])
          None => call("ConstNull", [con("T_func_ref")])
        }
      })
      let lim = call("Limit_t", [small_num(entries.length()), none_term(num)])
      let tab_t = call("T_tab", [lim, con("T_func_ref")])
      [@pair.mk_pair((tab_t, list_term(refs, hol_type("v_ref"))))]
    }
    None => []
  }
  let s = call("Wstore", [
    list_term(cls, hol_type("cl")),
    list_term(tab_items, ty(tabinst_ty)),
    list_term(mem_items, ty(mem_ty)),
    list_term(globs, hol_type("global")),
    list_term([], ty(eleminst_ty)),
    list_term([], ty(bytes)),
  ])
  (s, inst)
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
