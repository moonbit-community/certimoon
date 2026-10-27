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
  record_type("limit_t", "Limit_t", [("l_min", "Num"), ("l_max", "Option[Num]")])
  def("Ki64", "Ki64 == 65536")
  datatype("host", [("Host_func", ["Host_func"]), ("Host_ref", ["Host_ref"])])
  enum_type("t_num", ["T_i32", "T_i64", "T_f32", "T_f64"])
  enum_type("t_vec", ["T_v128"])
  enum_type("t_ref", ["T_func_ref", "T_ext_ref"])
  datatype("valtype", [
    ("T_num", ["T_num"]),
    ("T_vec", ["T_vec"]),
    ("T_ref", ["T_ref"]),
    ("T_bot", []),
  ])
  enum_type("tp_num", ["Tp_i8", "Tp_i16", "Tp_i32"])
  enum_type("tp_vec", ["Tp_v8_8", "Tp_v16_4", "Tp_v32_2"])
  enum_type("mut", ["T_immut", "T_mut"])
  record_type("tg", "Tg", [("tg_mut", "Mut"), ("tg_t", "Valtype")])
  // Isabelle: tf = Tf (dom) (ran), written t1s _> t2s
  record_type("tf", "Tf", [
    ("tf_dom", "List[Valtype]"),
    ("tf_ran", "List[Valtype]"),
  ])
  datatype("tb", [("Tbf", ["Num"]), ("Tbv", ["Option[Valtype]"])])
  datatype("tab_t", [("T_tab", ["Limit_t", "T_ref"])])
  def("tab_t_lim", "tab_t_lim(T_tab(lim, t)) == lim")
  def("tab_t_reftype", "tab_t_reftype(T_tab(lim, t)) == t")
  // data_t = unit, elem_t = t_ref
  record_type("t_context", "T_context", [
    ("ctx_types", "List[Tf]"),
    ("ctx_func", "List[Tf]"),
    ("ctx_global", "List[Tg]"),
    ("ctx_elem", "List[T_ref]"),
    ("ctx_data", "List[Unit]"),
    ("ctx_table", "List[Tab_t]"),
    ("ctx_memory", "List[Limit_t]"),
    ("ctx_local", "List[Valtype]"),
    ("ctx_label", "List[List[Valtype]]"),
    ("ctx_return", "Option[List[Valtype]]"),
    ("ctx_refs", "List[Num]"),
  ])
  datatype("v_num", [
    ("ConstInt32", ["\{w32}"]),
    ("ConstInt64", ["\{w64}"]),
    ("ConstFloat32", ["F32"]),
    ("ConstFloat64", ["F64"]),
  ])
  datatype("v_ref", [
    ("ConstNull", ["T_ref"]),
    ("ConstRefFunc", ["Num"]),
    ("ConstRefExtern", ["Host"]),
  ])
  datatype("v_vec", [("ConstVec128", ["V128"])])
  datatype("value", [
    ("V_num", ["V_num"]),
    ("V_vec", ["V_vec"]),
    ("V_ref", ["V_ref"]),
  ])
  enum_type("sx", ["S", "U"])
  enum_type("sat", ["Sat", "Nonsat"])
  enum_type("unop_i", ["Clz", "Ctz", "Popcnt"])
  enum_type("unop_f", [
    "Neg",
    "Abs",
    "Ceil",
    "Floor",
    "Trunc",
    "Nearest",
    "Sqrt",
  ])
  datatype("unop", [
    ("Unop_i", ["Unop_i"]),
    ("Unop_f", ["Unop_f"]),
    ("Extend_s", ["Tp_num"]),
  ])
  datatype("binop_i", [
    ("Add", []),
    ("Sub", []),
    ("Mul", []),
    ("Div", ["Sx"]),
    ("Rem", ["Sx"]),
    ("And", []),
    ("Or", []),
    ("Xor", []),
    ("Shl", []),
    ("Shr", ["Sx"]),
    ("Rotl", []),
    ("Rotr", []),
  ])
  enum_type("binop_f", [
    "Addf",
    "Subf",
    "Mulf",
    "Divf",
    "Min",
    "Max",
    "Copysign",
  ])
  datatype("binop", [("Binop_i", ["Binop_i"]), ("Binop_f", ["Binop_f"])])
  enum_type("testop", ["Eqz"])
  datatype("relop_i", [
    ("Eq", []),
    ("Ne", []),
    ("Lt", ["Sx"]),
    ("Gt", ["Sx"]),
    ("Le", ["Sx"]),
    ("Ge", ["Sx"]),
  ])
  enum_type("relop_f", ["Eqf", "Nef", "Ltf", "Gtf", "Lef", "Gef"])
  datatype("relop", [("Relop_i", ["Relop_i"]), ("Relop_f", ["Relop_f"])])
  enum_type("cvtop", ["Convert", "Reinterpret"])
  enum_type("shape_vec_i", ["I8_16", "I16_8", "I32_4", "I64_2"])
  enum_type("shape_vec_f", ["F32_4", "F64_2"])
  datatype("shape_vec", [("Svi", ["Shape_vec_i"]), ("Svf", ["Shape_vec_f"])])
  datatype("loadop_vec", [
    ("Load_128", []),
    ("Load_packed_vec", ["Tp_vec", "Sx"]),
    ("Load_32_zero", []),
    ("Load_64_zero", []),
    ("Load_splat", ["Shape_vec_i"]),
  ])
  datatype("storeop_vec", [
    ("Store_128", []),
    ("Store_lane", ["Shape_vec_i", "Num"]),
  ])
  // basic instructions (i, a, off are num)
  datatype("b_e", [
    ("Unreachable", []),
    ("Nop", []),
    ("Drop", []),
    ("Select", ["Option[Valtype]"]),
    ("Block", ["Tb", "List[B_e]"]),
    ("Loop", ["Tb", "List[B_e]"]),
    ("If", ["Tb", "List[B_e]", "List[B_e]"]),
    ("Br", ["Num"]),
    ("Br_if", ["Num"]),
    ("Br_table", ["List[Num]", "Num"]),
    ("Return", []),
    ("Call", ["Num"]),
    ("Call_indirect", ["Num", "Num"]),
    ("Local_get", ["Num"]),
    ("Local_set", ["Num"]),
    ("Local_tee", ["Num"]),
    ("Global_get", ["Num"]),
    ("Global_set", ["Num"]),
    ("Table_get", ["Num"]),
    ("Table_set", ["Num"]),
    ("Table_size", ["Num"]),
    ("Table_grow", ["Num"]),
    ("Load", ["T_num", "Option[(Tp_num, Sx)]", "Num", "Num"]),
    ("Store", ["T_num", "Option[Tp_num]", "Num", "Num"]),
    ("Load_vec", ["Loadop_vec", "Num", "Num"]),
    ("Load_lane_vec", ["Shape_vec_i", "Num", "Num", "Num"]),
    ("Store_vec", ["Storeop_vec", "Num", "Num"]),
    ("Memory_size", []),
    ("Memory_grow", []),
    ("Memory_init", ["Num"]),
    ("Memory_fill", []),
    ("Memory_copy", []),
    ("Table_init", ["Num", "Num"]),
    ("Table_copy", ["Num", "Num"]),
    ("Table_fill", ["Num"]),
    ("Elem_drop", ["Num"]),
    ("Data_drop", ["Num"]),
    ("EConstNum", ["V_num"]),
    ("EConstVec", ["V_vec"]),
    ("Unop", ["T_num", "Unop"]),
    ("Binop", ["T_num", "Binop"]),
    ("Testop", ["T_num", "Testop"]),
    ("Relop", ["T_num", "Relop"]),
    ("Cvtop", ["T_num", "Cvtop", "T_num", "Option[(Sat, Sx)]"]),
    ("Ref_null", ["T_ref"]),
    ("Ref_is_null", []),
    ("Ref_func", ["Num"]),
    ("Unop_vec", ["Unop_vec"]),
    ("Binop_vec", ["Binop_vec"]),
    ("Ternop_vec", ["Ternop_vec"]),
    ("Test_vec", ["Testop_vec"]),
    ("Shift_vec", ["Shiftop_vec"]),
    ("Splat_vec", ["Shape_vec"]),
    ("Extract_vec", ["Shape_vec", "Sx", "Num"]),
    ("Replace_vec", ["Shape_vec", "Num"]),
  ])
  record_type("inst", "Inst", [
    ("inst_types", "List[Tf]"),
    ("inst_funcs", "List[Num]"),
    ("inst_tabs", "List[Num]"),
    ("inst_mems", "List[Num]"),
    ("inst_globs", "List[Num]"),
    ("inst_elems", "List[Num]"),
    ("inst_datas", "List[Num]"),
  ])
  // function closures
  datatype("cl", [
    ("Func_native", ["Inst", "Tf", "List[Valtype]", "List[B_e]"]),
    ("Func_host", ["Tf", "Host"]),
  ])
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
  record_type("global", "Global", [("g_mut", "Mut"), ("g_val", "Value")])
  record_type("wstore", "Wstore", [
    ("s_funcs", "List[Cl]"),
    ("s_tabs", "List[\{tabinst_ty}]"),
    ("s_mems", "List[\{mem_ty}]"),
    ("s_globs", "List[Global]"),
    ("s_elems", "List[\{eleminst_ty}]"),
    ("s_datas", "List[\{bytes}]"),
  ])
  record_type("wframe", "Wframe", [("f_locs", "List[Value]"), ("f_inst", "Inst")])
  // administrative instructions (Isabelle writes Basic b as $b)
  datatype("einstr", [
    ("Basic", ["B_e"]),
    ("Trap", []),
    ("Invoke", ["Num"]),
    ("Label", ["Num", "List[Einstr]", "List[Einstr]"]),
    ("Frame", ["Num", "Wframe", "List[Einstr]"]),
    ("Ref", ["V_ref"]),
  ])
  // L0 = v* [<hole>] e*; L(i+1) = v* (label n {e*} Li) e*
  datatype("lholed", [
    ("LBase", ["List[Value]", "List[Einstr]"]),
    ("LRec", ["List[Value]", "Num", "List[Einstr]", "Lholed", "List[Einstr]"]),
  ])
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
