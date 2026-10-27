// WasmCert-Isabelle's Wasm_Ast.thy: the abstract syntax.
//
// Isabelle names are kept, except:
// - single-letter types: t -> valtype, v -> value, s -> wstore,
//   f -> wframe, e -> einstr (a one-letter type would take a type
//   variable's spelling);
// - records are one-constructor datatypes (`record_type`), and fields that
//   Isabelle tells apart by qualification get a prefix: t_context's fields
//   are ctx_*, inst's inst_*, s's s_*, f's f_* (local and return are MoonBit
//   keywords);
// - i32/i64 are the word types themselves (Isabelle copies them with
//   typedef and lifting), and bytes are 8-bit words (Isabelle's uint8).

///|
/// List and option functions Isabelle's library has and HOL Light's does
/// not, with Isabelle's names and meaning.
fn define_helpers() -> Unit raise {
  def(
    "take",
    "(take : (Num, List[A]) -> List[A])(0, l) == NIL && take(SUC(n), NIL) == NIL && take(SUC(n), CONS(h, t)) == CONS(h, take(n, t))",
  )
  def(
    "drop",
    "(drop : (Num, List[A]) -> List[A])(0, l) == l && drop(SUC(n), NIL) == NIL && drop(SUC(n), CONS(h, t)) == drop(n, t)",
  )
  def(
    "takefill",
    "(takefill : (A, Num, List[A]) -> List[A])(a, 0, l) == NIL && takefill(a, SUC(n), NIL) == CONS(a, takefill(a, n, NIL)) && takefill(a, SUC(n), CONS(h, t)) == CONS(h, takefill(a, n, t))",
  )
  // xs[i := x]
  def(
    "list_update",
    "(list_update : (List[A], Num, A) -> List[A])(NIL, i, x) == NIL && list_update(CONS(h, t), 0, x) == CONS(x, t) && list_update(CONS(h, t), SUC(n), x) == CONS(h, list_update(t, n, x))",
  )
  // [i..<j]
  def(
    "upt",
    "(upt : (Num, Num) -> List[Num])(i, 0) == NIL && upt(i, SUC(j)) == (if i <= j { APPEND(upt(i, j), [j]) } else { NIL })",
  )
  def(
    "concat",
    "(concat : (List[List[A]]) -> List[A])(NIL) == NIL && concat(CONS(l, ls)) == APPEND(l, concat(ls))",
  )
  def(
    "map_option",
    "(map_option : ((A) -> B, Option[A]) -> Option[B])(f, NONE) == NONE && map_option(f, SOME(x)) == SOME(f(x))",
  )
  def(
    "pred_option",
    "(pred_option : ((A) -> Bool, Option[A]) -> Bool)(p, NONE) == true && pred_option(p, SOME(x)) == p(x)",
  )
  def(
    "those",
    "(those : (List[Option[A]]) -> Option[List[A]])(NIL) == SOME(NIL) && those(CONS(x, xs)) == (match x { NONE => NONE; SOME(y) => map_option(CONS(y), those(xs)) })",
  )
}

///|
fn define_ast() -> Unit raise {
  // typedecl host_func, host_ref, host_state
  @kernel.new_type("host_func", 0L)
  @kernel.new_type("host_ref", 0L)
  @kernel.new_type("host_state", 0L)
  // f32, f64 and v128 are copies of the word types; their operations are
  // left unspecified (Wasm_Type_Abs.wasm_float, Wasm_Base_Defs consts)
  for p in [("f32", w32), ("f64", w64), ("v128", w128)] {
    let (name, w) = p
    let exists = @tactics.prove(
      tm("∃ x : \{w}, (UNIV : (\{w}) -> Bool)(x)"),
      @meson.meson_tac(@list.List([@sets.in_univ(), @sets.in_()])),
    )
    record(
      name + "_typedef",
      @class.new_type_definition(name, ("mk_" + name, "dest_" + name), exists),
    )
  }
  // The vector operators are opaque (Isabelle: typedefs of unspecified
  // finite sets of numbers; their finiteness only serves code export).
  for name in ["unop_vec", "binop_vec", "ternop_vec", "testop_vec", "shiftop_vec"] {
    @kernel.new_type(name, 0L)
  }
  record_type("limit_t", "Limit_t", [("l_min", "num"), ("l_max", "num option")])
  def("Ki64", "Ki64 == 65536")
  datatype("host", "host = Host_func host_func | Host_ref host_ref")
  datatype("t_num", "t_num = T_i32 | T_i64 | T_f32 | T_f64")
  datatype("t_vec", "t_vec = T_v128")
  datatype("t_ref", "t_ref = T_func_ref | T_ext_ref")
  datatype(
    "valtype",
    "valtype = T_num t_num | T_vec t_vec | T_ref t_ref | T_bot",
  )
  datatype("tp_num", "tp_num = Tp_i8 | Tp_i16 | Tp_i32")
  datatype("tp_vec", "tp_vec = Tp_v8_8 | Tp_v16_4 | Tp_v32_2")
  datatype("mut", "mut = T_immut | T_mut")
  record_type("tg", "Tg", [("tg_mut", "mut"), ("tg_t", "valtype")])
  // Isabelle: tf = Tf (dom) (ran), written t1s _> t2s
  record_type("tf", "Tf", [
    ("tf_dom", "valtype list"),
    ("tf_ran", "valtype list"),
  ])
  datatype("tb", "tb = Tbf num | Tbv (valtype option)")
  datatype("tab_t", "tab_t = T_tab limit_t t_ref")
  def("tab_t_lim", "tab_t_lim(T_tab(lim, t)) == lim")
  def("tab_t_reftype", "tab_t_reftype(T_tab(lim, t)) == t")
  // data_t = unit, elem_t = t_ref
  record_type("t_context", "T_context", [
    ("ctx_types", "tf list"),
    ("ctx_func", "tf list"),
    ("ctx_global", "tg list"),
    ("ctx_elem", "t_ref list"),
    ("ctx_data", "1 list"),
    ("ctx_table", "tab_t list"),
    ("ctx_memory", "limit_t list"),
    ("ctx_local", "valtype list"),
    ("ctx_label", "(valtype list) list"),
    ("ctx_return", "(valtype list) option"),
    ("ctx_refs", "num list"),
  ])
  datatype(
    "v_num",
    "v_num = ConstInt32 (32 word) | ConstInt64 (64 word) | ConstFloat32 f32 | ConstFloat64 f64",
  )
  datatype(
    "v_ref",
    "v_ref = ConstNull t_ref | ConstRefFunc num | ConstRefExtern host",
  )
  datatype("v_vec", "v_vec = ConstVec128 v128")
  datatype("value", "value = V_num v_num | V_vec v_vec | V_ref v_ref")
  datatype("sx", "sx = S | U")
  datatype("sat", "sat = Sat | Nonsat")
  datatype("unop_i", "unop_i = Clz | Ctz | Popcnt")
  datatype(
    "unop_f",
    "unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt",
  )
  datatype(
    "unop",
    "unop = Unop_i unop_i | Unop_f unop_f | Extend_s tp_num",
  )
  datatype(
    "binop_i",
    "binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr",
  )
  datatype(
    "binop_f",
    "binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign",
  )
  datatype("binop", "binop = Binop_i binop_i | Binop_f binop_f")
  datatype("testop", "testop = Eqz")
  datatype(
    "relop_i",
    "relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx",
  )
  datatype("relop_f", "relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef")
  datatype("relop", "relop = Relop_i relop_i | Relop_f relop_f")
  datatype("cvtop", "cvtop = Convert | Reinterpret")
  datatype("shape_vec_i", "shape_vec_i = I8_16 | I16_8 | I32_4 | I64_2")
  datatype("shape_vec_f", "shape_vec_f = F32_4 | F64_2")
  datatype(
    "shape_vec",
    "shape_vec = Svi shape_vec_i | Svf shape_vec_f",
  )
  datatype(
    "loadop_vec",
    "loadop_vec = Load_128 | Load_packed_vec tp_vec sx | Load_32_zero | Load_64_zero | Load_splat shape_vec_i",
  )
  datatype(
    "storeop_vec",
    "storeop_vec = Store_128 | Store_lane shape_vec_i num",
  )
  // basic instructions (i, a, off are num)
  datatype(
    "b_e",
    "b_e = Unreachable" +
    " | Nop" +
    " | Drop" +
    " | Select (valtype option)" +
    " | Block tb (b_e list)" +
    " | Loop tb (b_e list)" +
    " | If tb (b_e list) (b_e list)" +
    " | Br num" +
    " | Br_if num" +
    " | Br_table (num list) num" +
    " | Return" +
    " | Call num" +
    " | Call_indirect num num" +
    " | Local_get num" +
    " | Local_set num" +
    " | Local_tee num" +
    " | Global_get num" +
    " | Global_set num" +
    " | Table_get num" +
    " | Table_set num" +
    " | Table_size num" +
    " | Table_grow num" +
    " | Load t_num ((tp_num # sx) option) num num" +
    " | Store t_num (tp_num option) num num" +
    " | Load_vec loadop_vec num num" +
    " | Load_lane_vec shape_vec_i num num num" +
    " | Store_vec storeop_vec num num" +
    " | Memory_size" +
    " | Memory_grow" +
    " | Memory_init num" +
    " | Memory_fill" +
    " | Memory_copy" +
    " | Table_init num num" +
    " | Table_copy num num" +
    " | Table_fill num" +
    " | Elem_drop num" +
    " | Data_drop num" +
    " | EConstNum v_num" +
    " | EConstVec v_vec" +
    " | Unop t_num unop" +
    " | Binop t_num binop" +
    " | Testop t_num testop" +
    " | Relop t_num relop" +
    " | Cvtop t_num cvtop t_num ((sat # sx) option)" +
    " | Ref_null t_ref" +
    " | Ref_is_null" +
    " | Ref_func num" +
    " | Unop_vec unop_vec" +
    " | Binop_vec binop_vec" +
    " | Ternop_vec ternop_vec" +
    " | Test_vec testop_vec" +
    " | Shift_vec shiftop_vec" +
    " | Splat_vec shape_vec" +
    " | Extract_vec shape_vec sx num" +
    " | Replace_vec shape_vec num",
  )
  record_type("inst", "Inst", [
    ("inst_types", "tf list"),
    ("inst_funcs", "num list"),
    ("inst_tabs", "num list"),
    ("inst_mems", "num list"),
    ("inst_globs", "num list"),
    ("inst_elems", "num list"),
    ("inst_datas", "num list"),
  ])
  // function closures
  datatype(
    "cl",
    "cl = Func_native inst tf (valtype list) (b_e list) | Func_host tf host",
  )
  // tabinst = tab_t * v_ref list; eleminst = elem_t * v_ref list;
  // datainst = bytes
  def("tab_size", "tab_size((t : \{tabinst_ty})) == LENGTH(SND(t))")
  def(
    "tab_max",
    "tab_max((t : \{tabinst_ty})) == l_max(tab_t_lim(FST(t)))",
  )
  def(
    "tab_reftype",
    "tab_reftype((t : \{tabinst_ty})) == tab_t_reftype(FST(t))",
  )
  record_type("global", "Global", [("g_mut", "mut"), ("g_val", "value")])
  record_type("wstore", "Wstore", [
    ("s_funcs", "cl list"),
    ("s_tabs", "(tab_t # v_ref list) list"),
    ("s_mems", "(limit_t # (8 word) list) list"),
    ("s_globs", "global list"),
    ("s_elems", "(t_ref # v_ref list) list"),
    ("s_datas", "((8 word) list) list"),
  ])
  record_type("wframe", "Wframe", [("f_locs", "value list"), ("f_inst", "inst")])
  // administrative instructions (Isabelle writes Basic b as $b)
  datatype(
    "einstr",
    "einstr = Basic b_e | Trap | Invoke num | Label num (einstr list) (einstr list) | Frame num wframe (einstr list) | Ref v_ref",
  )
  // L0 = v* [<hole>] e*; L(i+1) = v* (label n {e*} Li) e*
  datatype(
    "lholed",
    "lholed = LBase (value list) (einstr list) | LRec (value list) num (einstr list) lholed (einstr list)",
  )
}

///|
/// Wasm_Ast's byte and memory functions.
fn define_memory() -> Unit raise {
  def("msb_byte", "msb_byte((b : \{w8})) == bit(7, b)")
  def("zero_byte", "zero_byte == (word : (Num) -> \{w8})(0)")
  def("negone_byte", "negone_byte == word_not((word : (Num) -> \{w8})(0))")
  def("nat_of_byte", "nat_of_byte((b : \{w8})) == val(b)")
  def("byte_of_nat", "byte_of_nat(n) == (word : (Num) -> \{w8})(n)")
  def(
    "bytes_takefill",
    "bytes_takefill((a : \{w8}), n, as_) == takefill(a, n, as_)",
  )
  def(
    "bytes_replicate",
    "bytes_replicate(n, (b : \{w8})) == REPLICATE(n, b)",
  )
  def("msbyte", "msbyte((bs : \{bytes})) == LAST(bs)")
  def(
    "mem_rep_mk",
    "mem_rep_mk(n) == bytes_replicate(n * Ki64, zero_byte)",
  )
  def("mem_mk", "mem_mk(lim) == (lim, mem_rep_mk(l_min(lim)))")
  def("byte_at", "byte_at((m : \{mem_ty}), n) == EL(n, SND(m))")
  def("mem_length", "mem_length((m : \{mem_ty})) == LENGTH(SND(m))")
  def("mem_max", "mem_max((m : \{mem_ty})) == l_max(FST(m))")
  def(
    "read_bytes",
    "read_bytes((m : \{mem_ty}), n, l) == take(l, drop(n, SND(m)))",
  )
  def(
    "write_bytes",
    "write_bytes((m : \{mem_ty}), n, bs) == (FST(m), APPEND(take(n, SND(m)), APPEND(bs, drop(n + LENGTH(bs), SND(m)))))",
  )
  def(
    "mem_append",
    "mem_append((m : \{mem_ty}), n, (b : \{w8})) == (l_min_update(l_min(FST(m)) + DIV(n, Ki64), FST(m)), APPEND(SND(m), REPLICATE(n, b)))",
  )
}
