// The numeric layer: Wasm_Type_Abs, Wasm_Type_Word and the numeric part of
// Wasm_Base_Defs.
//
// Integers are N-bit words (Library/words), and each operation is the
// word function Wasm_Type_Word.Wasm_Int_Word implements it with:
// shifts and rotations take the count modulo the width (word_jshl,
// word_jushr, word_jshr, word_jrol, word_jror), signed division and
// remainder truncate towards zero (word_jdiv, word_jrem: Isabelle's sdiv
// and smod). Isabelle's class wasm_int states the specification these
// meet; proving that is left for later. Floats and vector operations are
// unspecified, as in Isabelle.

///|
fn define_int_ops() -> Unit raise {
  def(
    "int_clz",
    "int_clz((x : Word[N])) == (word : (Num) -> Word[N])(word_clz(x))",
  )
  def(
    "int_ctz",
    "int_ctz((x : Word[N])) == (word : (Num) -> Word[N])(word_ctz(x))",
  )
  def(
    "int_popcnt",
    "int_popcnt((x : Word[N])) == (word : (Num) -> Word[N])(word_popcount(x))",
  )
  def(
    "int_div_u",
    "int_div_u((x : Word[N]), y) == (if y == word(0) { NONE } else { SOME(word_udiv(x, y)) })",
  )
  // None on division by zero and on the one quotient that overflows,
  // INT_MIN / -1
  def(
    "int_div_s",
    "int_div_s((x : Word[N]), y) == (if y == word(0) || (x == word(EXP(2, dimindex((UNIV : (N) -> Bool)) - 1)) && y == word_not(word(0))) { NONE } else { SOME(word_jdiv(x, y)) })",
  )
  def(
    "int_rem_u",
    "int_rem_u((x : Word[N]), y) == (if y == word(0) { NONE } else { SOME(word_umod(x, y)) })",
  )
  def(
    "int_rem_s",
    "int_rem_s((x : Word[N]), y) == (if y == word(0) { NONE } else { SOME(word_jrem(x, y)) })",
  )
  def("int_eqz", "int_eqz((x : Word[N])) == (x == word(0))")
}

///|
/// Isabelle's wasm_float class parameters and the conversions it declares
/// with consts: uninterpreted, and polymorphic where Isabelle overloads.
fn define_float_ops() -> Unit raise {
  for op in [
      "float_neg", "float_abs", "float_ceil", "float_floor", "float_trunc", "float_nearest",
      "float_sqrt",
    ] {
    constant(op, "(A) -> A")
  }
  for op in [
      "float_add", "float_sub", "float_mul", "float_div", "float_min", "float_max", "float_copysign",
    ] {
    constant(op, "(A, A) -> A")
  }
  for op in ["float_eq", "float_lt", "float_gt", "float_le", "float_ge"] {
    constant(op, "(A, A) -> Bool")
  }
  // the zeros of f32, f64 and v128 (Isabelle instantiates the zero class
  // for them without defining it)
  constant("zero_f32", "F32")
  constant("zero_f64", "F64")
  constant("zero_v128", "V128")
  // vector operations
  constant("binop_vec_wf", "(Binop_vec) -> Bool")
  constant("app_unop_vec_v", "(Unop_vec, V128) -> V128")
  constant("app_binop_vec_v", "(Binop_vec, V128, V128) -> Option[V128]")
  constant("app_shuffle_vec_v", "(List[Num], V128, V128) -> V128")
  constant("app_ternop_vec_v", "(Ternop_vec, V128, V128, V128) -> V128")
  constant("app_test_vec_v", "(Testop_vec, V128) -> \{w32}")
  constant("app_shift_vec_v", "(Shiftop_vec, V128, \{w32}) -> V128")
  // float to int, trapping and saturating
  for p in [("i32", w32), ("i64", w64)] {
    let (i, w) = p
    for f in ["f32", "f64"] {
      let ft = if f == "f32" { "F32" } else { "F64" }
      for sign in ["u", "s"] {
        constant("\{sign}\{i}_trunc_\{f}", "(\{ft}) -> Option[\{w}]")
        constant("\{sign}\{i}_trunc_sat_\{f}", "(\{ft}) -> \{w}")
      }
    }
  }
  // int to float
  for f in ["f32", "f64"] {
    let ft = if f == "f32" { "F32" } else { "F64" }
    for p in [("i32", w32), ("i64", w64)] {
      for sign in ["u", "s"] {
        constant("\{f}_convert_\{sign}\{p.0}", "(\{p.1}) -> \{ft}")
      }
    }
  }
  constant("wasm_demote", "(F64) -> F32")
  constant("wasm_promote", "(F32) -> F64")
  constant("deserialise_f32", "(\{bytes}) -> F32")
  constant("deserialise_f64", "(\{bytes}) -> F64")
  constant("deserialise_v128", "(\{bytes}) -> V128")
  // serialise_f32 x has 4 bytes, and so on (Isabelle: specification)
  for p in [("f32", "F32", 4), ("f64", "F64", 8), ("v128", "V128", 16)] {
    let (name, t, n) = p
    let exists = @tactics.prove(
      tm(
        "∃ f : (\{t}) -> \{bytes}, ∀ x : \{t}, LENGTH(f(x)) == \{n}",
      ),
      @tactics.then_tac(
        @tactics.exists_tac(
          tm("(x : \{t}) => REPLICATE(\{n}, (word : (Num) -> \{w8})(0))"),
        ),
        @simp.rewrite_tac(@list.List([@lists.length_replicate()])),
      ),
    )
    record(
      "serialise_" + name + "_len",
      @nums.new_specification(@list.List(["serialise_" + name]))(exists),
    )
  }
}

///|
/// Wasm_Base_Defs: conversions between widths and byte encodings.
fn define_conversions() -> Unit raise {
  def("wasm_wrap", "wasm_wrap((c : \{w64})) == (word_zx(c) : \{w32})")
  def("wasm_extend_u", "wasm_extend_u((c : \{w32})) == (word_zx(c) : \{w64})")
  def("wasm_extend_s", "wasm_extend_s((c : \{w32})) == (word_sx(c) : \{w64})")
  // little-endian bytes (Isabelle: word_rsplit_rev, word_rcat_rev)
  def(
    "le_bytes",
    "(le_bytes : (Num, Num) -> \{bytes})(0, n) == NIL && le_bytes(SUC(k), n) == CONS(word(n), le_bytes(k, DIV(n, 256)))",
  )
  def(
    "num_of_bytes",
    "(num_of_bytes : (\{bytes}) -> Num)(NIL) == 0 && num_of_bytes(CONS(b, bs)) == val(b) + 256 * num_of_bytes(bs)",
  )
  def("serialise_i32", "serialise_i32((c : \{w32})) == le_bytes(4, val(c))")
  def("serialise_i64", "serialise_i64((c : \{w64})) == le_bytes(8, val(c))")
  def(
    "deserialise_i32",
    "deserialise_i32((bs : \{bytes})) == (word(num_of_bytes(bs)) : \{w32})",
  )
  def(
    "deserialise_i64",
    "deserialise_i64((bs : \{bytes})) == (word(num_of_bytes(bs)) : \{w64})",
  )
  def(
    "wasm_bool",
    "wasm_bool(b) == (if b { (word : (Num) -> \{w32})(1) } else { word(0) })",
  )
  def(
    "int32_minus_one",
    "int32_minus_one == word_not((word : (Num) -> \{w32})(0))",
  )
}

///|
/// Wasm_Base_Defs: memories and tables.
fn define_mem_tab() -> Unit raise {
  def("mem_size", "mem_size(m) == DIV(mem_length(m), Ki64)")
  def(
    "mem_grow",
    "mem_grow(m, n) == (if mem_size(m) + n <= 65536 && pred_option((max : Num) => mem_size(m) + n <= max, mem_max(m)) { SOME(mem_append(m, n * Ki64, zero_byte)) } else { NONE })",
  )
  def(
    "load",
    "load(m, n, off, l) == (if n + off + l <= mem_length(m) { SOME(read_bytes(m, n + off, l)) } else { NONE })",
  )
  def(
    "sign_extend",
    "sign_extend(U, l, bs) == bytes_takefill(zero_byte, l, bs) && sign_extend(S, l, bs) == bytes_takefill(if msb_byte(msbyte(bs)) { negone_byte } else { zero_byte }, l, bs)",
  )
  def(
    "load_packed",
    "load_packed(sx, m, n, off, lp, l) == map_option(sign_extend(sx, l), load(m, n, off, lp))",
  )
  def(
    "store",
    "store(m, n, off, bs, l) == (if n + off + l <= mem_length(m) { SOME(write_bytes(m, n + off, bytes_takefill(zero_byte, l, bs))) } else { NONE })",
  )
  def(
    "store_packed",
    "store_packed(m, n, off, bs, l) == store(m, n, off, bs, l)",
  )
  def(
    "store_tab_list",
    "store_tab_list(tab, n, vrs) == (if n + LENGTH(vrs) <= tab_size(tab) { SOME((FST(tab), APPEND(take(n, SND(tab)), APPEND(vrs, drop(n + LENGTH(vrs), SND(tab)))))) } else { NONE })",
  )
  def(
    "store_tab1",
    "store_tab1(tab, n, vr) == (if n < tab_size(tab) { SOME((FST(tab), APPEND(take(n, SND(tab)), APPEND([vr], drop(n + 1, SND(tab)))))) } else { NONE })",
  )
  def(
    "load_tabs1",
    "load_tabs1(tables, ti, n) == (if n < tab_size(EL(ti, tables)) { SOME(EL(n, SND(EL(ti, tables)))) } else { NONE })",
  )
  def(
    "store_tabs1",
    "store_tabs1(tables, ti, n, vr) == (match store_tab1(EL(ti, tables), n, vr) { SOME(tab') => SOME(APPEND(take(ti, tables), APPEND([tab'], drop(ti + 1, tables)))); NONE => NONE })",
  )
  def(
    "grow_tab",
    "grow_tab(t, n, vr) == (if tab_size(t) + n < EXP(2, 32) && pred_option((max : Num) => tab_size(t) + n <= max, tab_max(t)) { SOME((T_tab(l_min_update(tab_size(t) + n, tab_t_lim(FST(t))), tab_t_reftype(FST(t))), APPEND(SND(t), REPLICATE(n, vr)))) } else { NONE })",
  )
  // the host's functions, as a relation (Isabelle: consts)
  constant(
    "host_func_apply",
    "(Wstore, Tf, Host_func, List[Value], Host_state, Option[(Wstore, List[Value])]) -> Bool",
  )
}

///|
/// Wasm_Base_Defs: values, types and their sizes.
fn define_values() -> Unit raise {
  def(
    "wasm_deserialise_num",
    "wasm_deserialise_num(bs, T_i32) == ConstInt32(deserialise_i32(bs)) && wasm_deserialise_num(bs, T_i64) == ConstInt64(deserialise_i64(bs)) && wasm_deserialise_num(bs, T_f32) == ConstFloat32(deserialise_f32(bs)) && wasm_deserialise_num(bs, T_f64) == ConstFloat64(deserialise_f64(bs))",
  )
  def(
    "wasm_deserialise",
    "wasm_deserialise(bs, T_num(tn)) == V_num(wasm_deserialise_num(bs, tn)) && wasm_deserialise(bs, T_vec(tv)) == V_vec(ConstVec128(deserialise_v128(bs)))",
  )
  def(
    "bits_num",
    "bits_num(ConstInt32(c1)) == serialise_i32(c1) && bits_num(ConstInt64(c2)) == serialise_i64(c2) && bits_num(ConstFloat32(c3)) == serialise_f32(c3) && bits_num(ConstFloat64(c4)) == serialise_f64(c4)",
  )
  def("bits_vec", "bits_vec(ConstVec128(c)) == serialise_v128(c)")
  def(
    "bits",
    "bits(V_num(vn)) == bits_num(vn) && bits(V_vec(vv)) == bits_vec(vv)",
  )
  def(
    "bitzero_num",
    "bitzero_num(T_i32) == ConstInt32(word(0)) && bitzero_num(T_i64) == ConstInt64(word(0)) && bitzero_num(T_f32) == ConstFloat32(zero_f32) && bitzero_num(T_f64) == ConstFloat64(zero_f64)",
  )
  def("bitzero_vec", "bitzero_vec(T_v128) == ConstVec128(zero_v128)")
  def(
    "bitzero_ref",
    "bitzero_ref(T_func_ref) == ConstNull(T_func_ref) && bitzero_ref(T_ext_ref) == ConstNull(T_ext_ref)",
  )
  def(
    "bitzero",
    "bitzero(T_num(tn)) == SOME(V_num(bitzero_num(tn))) && bitzero(T_vec(tv)) == SOME(V_vec(bitzero_vec(tv))) && bitzero(T_ref(tr)) == SOME(V_ref(bitzero_ref(tr))) && bitzero(T_bot) == NONE",
  )
  def("n_zeros", "n_zeros(ts) == those(MAP(bitzero, ts))")
  def(
    "typeof_num",
    "typeof_num(ConstInt32(c1)) == T_i32 && typeof_num(ConstInt64(c2)) == T_i64 && typeof_num(ConstFloat32(c3)) == T_f32 && typeof_num(ConstFloat64(c4)) == T_f64",
  )
  def("typeof_vec", "typeof_vec(ConstVec128(c)) == T_v128")
  def(
    "typeof_ref",
    "typeof_ref(ConstRefFunc(i)) == T_func_ref && typeof_ref(ConstRefExtern(h)) == T_ext_ref && typeof_ref(ConstNull(t)) == t",
  )
  def(
    "is_null_ref",
    "is_null_ref(ConstNull(t)) == true && is_null_ref(ConstRefFunc(i)) == false && is_null_ref(ConstRefExtern(h)) == false",
  )
  // Isabelle's typeof (a MoonBit keyword)
  def(
    "typeof_v",
    "typeof_v(V_num(vn)) == T_num(typeof_num(vn)) && typeof_v(V_vec(vv)) == T_vec(typeof_vec(vv)) && typeof_v(V_ref(vr)) == T_ref(typeof_ref(vr))",
  )
  for p in [("is_num_type", "T_num"), ("is_vec_type", "T_vec"), ("is_ref_type", "T_ref")] {
    let clauses = ["T_num(tn)", "T_vec(tv)", "T_ref(tr)", "T_bot"].map(c => {
      let yes = c.has_prefix(p.1 + "(")
      "\{p.0}(\{c}) == \{yes}"
    })
    def(p.0, clauses.join(" && "))
  }
  def(
    "vec_lane_t",
    "vec_lane_t(Svi(I8_16)) == T_i32 && vec_lane_t(Svi(I16_8)) == T_i32 && vec_lane_t(Svi(I32_4)) == T_i32 && vec_lane_t(Svi(I64_2)) == T_i64 && vec_lane_t(Svf(F32_4)) == T_f32 && vec_lane_t(Svf(F64_2)) == T_f64",
  )
  def(
    "vec_i_length",
    "vec_i_length(I8_16) == 1 && vec_i_length(I16_8) == 2 && vec_i_length(I32_4) == 4 && vec_i_length(I64_2) == 8",
  )
  def("vec_f_length", "vec_f_length(F32_4) == 4 && vec_f_length(F64_2) == 8")
  def(
    "vec_length",
    "vec_length(Svi(svi)) == vec_i_length(svi) && vec_length(Svf(svf)) == vec_f_length(svf)",
  )
  def(
    "vec_i_num",
    "vec_i_num(I8_16) == 16 && vec_i_num(I16_8) == 8 && vec_i_num(I32_4) == 4 && vec_i_num(I64_2) == 2",
  )
  def("vec_f_num", "vec_f_num(F32_4) == 4 && vec_f_num(F64_2) == 2")
  def(
    "vec_num",
    "vec_num(Svi(svi)) == vec_i_num(svi) && vec_num(Svf(svf)) == vec_f_num(svf)",
  )
  def("option_projl", "option_projl((x : Option[(A, B)])) == map_option(FST, x)")
  def("option_projr", "option_projr((x : Option[(A, B)])) == map_option(SND, x)")
  def(
    "t_num_length",
    "t_num_length(T_i32) == 4 && t_num_length(T_i64) == 8 && t_num_length(T_f32) == 4 && t_num_length(T_f64) == 8",
  )
  def("t_vec_length", "t_vec_length(T_v128) == 16")
  def(
    "t_length",
    "t_length(T_num(tn)) == t_num_length(tn) && t_length(T_vec(tv)) == t_vec_length(tv)",
  )
  def(
    "tp_num_length",
    "tp_num_length(Tp_i8) == 1 && tp_num_length(Tp_i16) == 2 && tp_num_length(Tp_i32) == 4",
  )
  def(
    "tp_vec_length",
    "tp_vec_length(Tp_v8_8) == 1 && tp_vec_length(Tp_v16_4) == 2 && tp_vec_length(Tp_v32_2) == 4",
  )
  def(
    "tp_vec_num",
    "tp_vec_num(Tp_v8_8) == 8 && tp_vec_num(Tp_v16_4) == 4 && tp_vec_num(Tp_v32_2) == 2",
  )
  def(
    "is_int_t_num",
    "is_int_t_num(T_i32) == true && is_int_t_num(T_i64) == true && is_int_t_num(T_f32) == false && is_int_t_num(T_f64) == false",
  )
  def(
    "is_float_t_num",
    "is_float_t_num(T_i32) == false && is_float_t_num(T_i64) == false && is_float_t_num(T_f32) == true && is_float_t_num(T_f64) == true",
  )
  def("is_mut", "is_mut(tg) == (tg_mut(tg) == T_mut)")
  def(
    "unop_t_num_agree",
    "unop_t_num_agree(Unop_i(iop), t) == is_int_t_num(t) && unop_t_num_agree(Unop_f(fop), t) == is_float_t_num(t) && unop_t_num_agree(Extend_s(tp), t) == (is_int_t_num(t) && t_num_length(t) > tp_num_length(tp))",
  )
  def(
    "binop_t_num_agree",
    "binop_t_num_agree(Binop_i(iop), t) == is_int_t_num(t) && binop_t_num_agree(Binop_f(fop), t) == is_float_t_num(t)",
  )
  def(
    "relop_t_num_agree",
    "relop_t_num_agree(Relop_i(iop), t) == is_int_t_num(t) && relop_t_num_agree(Relop_f(fop), t) == is_float_t_num(t)",
  )
}

///|
/// Wasm_Base_Defs: applying the numeric operators.
fn define_app_ops() -> Unit raise {
  def(
    "app_unop_i",
    "(app_unop_i : (Unop_i, Word[N]) -> Word[N])(Ctz, c) == int_ctz(c) && app_unop_i(Clz, c) == int_clz(c) && app_unop_i(Popcnt, c) == int_popcnt(c)",
  )
  def(
    "app_unop_i_v",
    "app_unop_i_v(iop, ConstInt32(c1)) == ConstInt32(app_unop_i(iop, c1)) && app_unop_i_v(iop, ConstInt64(c2)) == ConstInt64(app_unop_i(iop, c2)) && app_unop_i_v(iop, ConstFloat32(c3)) == ConstFloat32(c3) && app_unop_i_v(iop, ConstFloat64(c4)) == ConstFloat64(c4)",
  )
  def(
    "app_unop_f",
    "(app_unop_f : (Unop_f, A) -> A)(Neg, c) == float_neg(c) && app_unop_f(Abs, c) == float_abs(c) && app_unop_f(Ceil, c) == float_ceil(c) && app_unop_f(Floor, c) == float_floor(c) && app_unop_f(Trunc, c) == float_trunc(c) && app_unop_f(Nearest, c) == float_nearest(c) && app_unop_f(Sqrt, c) == float_sqrt(c)",
  )
  def(
    "app_unop_f_v",
    "app_unop_f_v(fop, ConstFloat32(c3)) == ConstFloat32(app_unop_f(fop, c3)) && app_unop_f_v(fop, ConstFloat64(c4)) == ConstFloat64(app_unop_f(fop, c4)) && app_unop_f_v(fop, ConstInt32(c1)) == ConstInt32(c1) && app_unop_f_v(fop, ConstInt64(c2)) == ConstInt64(c2)",
  )
  def(
    "app_extend_s",
    "app_extend_s(tp, v) == wasm_deserialise_num(sign_extend(S, t_num_length(typeof_num(v)), take(tp_num_length(tp), bits_num(v))), typeof_num(v))",
  )
  def(
    "app_unop",
    "app_unop(Unop_i(iop), v) == app_unop_i_v(iop, v) && app_unop(Unop_f(fop), v) == app_unop_f_v(fop, v) && app_unop(Extend_s(tp), v) == app_extend_s(tp, v)",
  )
  def(
    "app_binop_i",
    "(app_binop_i : (Binop_i, Word[N], Word[N]) -> Option[Word[N]])(Add, c1, c2) == SOME(word_add(c1, c2))" +
    " && app_binop_i(Sub, c1, c2) == SOME(word_sub(c1, c2))" +
    " && app_binop_i(Mul, c1, c2) == SOME(word_mul(c1, c2))" +
    " && app_binop_i(Div(U), c1, c2) == int_div_u(c1, c2)" +
    " && app_binop_i(Div(S), c1, c2) == int_div_s(c1, c2)" +
    " && app_binop_i(Rem(U), c1, c2) == int_rem_u(c1, c2)" +
    " && app_binop_i(Rem(S), c1, c2) == int_rem_s(c1, c2)" +
    " && app_binop_i(And, c1, c2) == SOME(word_and(c1, c2))" +
    " && app_binop_i(Or, c1, c2) == SOME(word_or(c1, c2))" +
    " && app_binop_i(Xor, c1, c2) == SOME(word_xor(c1, c2))" +
    " && app_binop_i(Shl, c1, c2) == SOME(word_jshl(c1, c2))" +
    " && app_binop_i(Shr(U), c1, c2) == SOME(word_jushr(c1, c2))" +
    " && app_binop_i(Shr(S), c1, c2) == SOME(word_jshr(c1, c2))" +
    " && app_binop_i(Rotl, c1, c2) == SOME(word_jrol(c1, c2))" +
    " && app_binop_i(Rotr, c1, c2) == SOME(word_jror(c1, c2))",
  )
  def(
    "app_binop_i_v",
    "app_binop_i_v(iop, v1, v2) == (match (v1, v2) { (ConstInt32(a1), ConstInt32(a2)) => map_option(ConstInt32, app_binop_i(iop, a1, a2)); (ConstInt64(b1), ConstInt64(b2)) => map_option(ConstInt64, app_binop_i(iop, b1, b2)); other => NONE })",
  )
  def(
    "app_binop_f",
    "(app_binop_f : (Binop_f, A, A) -> Option[A])(Addf, c1, c2) == SOME(float_add(c1, c2))" +
    " && app_binop_f(Subf, c1, c2) == SOME(float_sub(c1, c2))" +
    " && app_binop_f(Mulf, c1, c2) == SOME(float_mul(c1, c2))" +
    " && app_binop_f(Divf, c1, c2) == SOME(float_div(c1, c2))" +
    " && app_binop_f(Min, c1, c2) == SOME(float_min(c1, c2))" +
    " && app_binop_f(Max, c1, c2) == SOME(float_max(c1, c2))" +
    " && app_binop_f(Copysign, c1, c2) == SOME(float_copysign(c1, c2))",
  )
  def(
    "app_binop_f_v",
    "app_binop_f_v(fop, v1, v2) == (match (v1, v2) { (ConstFloat32(a1), ConstFloat32(a2)) => map_option(ConstFloat32, app_binop_f(fop, a1, a2)); (ConstFloat64(b1), ConstFloat64(b2)) => map_option(ConstFloat64, app_binop_f(fop, b1, b2)); other => NONE })",
  )
  def(
    "app_binop",
    "app_binop(Binop_i(iop), v1, v2) == app_binop_i_v(iop, v1, v2) && app_binop(Binop_f(fop), v1, v2) == app_binop_f_v(fop, v1, v2)",
  )
  def("app_testop_i", "(app_testop_i : (Testop, Word[N]) -> Bool)(Eqz, c) == int_eqz(c)")
  def(
    "app_testop",
    "app_testop(op, ConstInt32(c1)) == ConstInt32(wasm_bool(app_testop_i(op, c1))) && app_testop(op, ConstInt64(c2)) == ConstInt32(wasm_bool(app_testop_i(op, c2))) && app_testop(op, ConstFloat32(c3)) == ConstInt32(word(0)) && app_testop(op, ConstFloat64(c4)) == ConstInt32(word(0))",
  )
  def(
    "app_relop_i",
    "(app_relop_i : (Relop_i, Word[N], Word[N]) -> Bool)(Eq, c1, c2) == (c1 == c2)" +
    " && app_relop_i(Ne, c1, c2) == (c1 != c2)" +
    " && app_relop_i(Lt(U), c1, c2) == word_ult(c1, c2)" +
    " && app_relop_i(Lt(S), c1, c2) == word_ilt(c1, c2)" +
    " && app_relop_i(Gt(U), c1, c2) == word_ugt(c1, c2)" +
    " && app_relop_i(Gt(S), c1, c2) == word_igt(c1, c2)" +
    " && app_relop_i(Le(U), c1, c2) == word_ule(c1, c2)" +
    " && app_relop_i(Le(S), c1, c2) == word_ile(c1, c2)" +
    " && app_relop_i(Ge(U), c1, c2) == word_uge(c1, c2)" +
    " && app_relop_i(Ge(S), c1, c2) == word_ige(c1, c2)",
  )
  def(
    "app_relop_i_v",
    "app_relop_i_v(iop, v1, v2) == (match (v1, v2) { (ConstInt32(a1), ConstInt32(a2)) => ConstInt32(wasm_bool(app_relop_i(iop, a1, a2))); (ConstInt64(b1), ConstInt64(b2)) => ConstInt32(wasm_bool(app_relop_i(iop, b1, b2))); other => ConstInt32(word(0)) })",
  )
  def(
    "app_relop_f",
    "(app_relop_f : (Relop_f, A, A) -> Bool)(Eqf, c1, c2) == float_eq(c1, c2)" +
    " && app_relop_f(Nef, c1, c2) == !float_eq(c1, c2)" +
    " && app_relop_f(Ltf, c1, c2) == float_lt(c1, c2)" +
    " && app_relop_f(Gtf, c1, c2) == float_gt(c1, c2)" +
    " && app_relop_f(Lef, c1, c2) == float_le(c1, c2)" +
    " && app_relop_f(Gef, c1, c2) == float_ge(c1, c2)",
  )
  def(
    "app_relop_f_v",
    "app_relop_f_v(fop, v1, v2) == (match (v1, v2) { (ConstFloat32(a1), ConstFloat32(a2)) => ConstInt32(wasm_bool(app_relop_f(fop, a1, a2))); (ConstFloat64(b1), ConstFloat64(b2)) => ConstInt32(wasm_bool(app_relop_f(fop, b1, b2))); other => ConstInt32(word(0)) })",
  )
  def(
    "app_relop",
    "app_relop(Relop_i(iop), v1, v2) == app_relop_i_v(iop, v1, v2) && app_relop(Relop_f(fop), v1, v2) == app_relop_f_v(fop, v1, v2)",
  )
}

///|
/// Wasm_Base_Defs: vector operations and vector memory access.
fn define_vec_ops() -> Unit raise {
  def(
    "insert_lane_vec_bs",
    "insert_lane_vec_bs(len_lane, i, (bs_lane : \{bytes}), bs_vec) == APPEND(take(i * len_lane, bs_vec), APPEND(take(len_lane, bs_lane), drop((i + 1) * len_lane, bs_vec)))",
  )
  def(
    "app_unop_vec",
    "app_unop_vec(uop, ConstVec128(c)) == ConstVec128(app_unop_vec_v(uop, c))",
  )
  def(
    "app_binop_vec",
    "app_binop_vec(bop, ConstVec128(c1), ConstVec128(c2)) == map_option(ConstVec128, app_binop_vec_v(bop, c1, c2))",
  )
  def(
    "app_shuffle_vec",
    "app_shuffle_vec(is_, ConstVec128(c1), ConstVec128(c2)) == ConstVec128(app_shuffle_vec_v(is_, c1, c2))",
  )
  def(
    "app_ternop_vec",
    "app_ternop_vec(op, ConstVec128(c1), ConstVec128(c2), ConstVec128(c3)) == ConstVec128(app_ternop_vec_v(op, c1, c2, c3))",
  )
  def(
    "app_test_vec",
    "app_test_vec(op, ConstVec128(c)) == app_test_vec_v(op, c)",
  )
  def(
    "app_shift_vec",
    "app_shift_vec(sop, ConstVec128(cv), cn) == ConstVec128(app_shift_vec_v(sop, cv, cn))",
  )
  def(
    "app_splat_vec",
    "app_splat_vec(sv, v) == ConstVec128(deserialise_v128(concat(REPLICATE(vec_num(sv), take(vec_length(sv), bits_num(v))))))",
  )
  // the bytes of lane i (Isabelle's let-bound bs_n in app_extract_vec)
  def(
    "lane_bytes",
    "lane_bytes(sv, i, vv) == take(vec_length(sv), drop(i * vec_length(sv), bits_vec(vv)))",
  )
  def(
    "app_extract_vec",
    "app_extract_vec(Svi(I8_16), sx, i, vv) == ConstInt32(deserialise_i32(sign_extend(sx, 4, lane_bytes(Svi(I8_16), i, vv))))" +
    " && app_extract_vec(Svi(I16_8), sx, i, vv) == ConstInt32(deserialise_i32(sign_extend(sx, 4, lane_bytes(Svi(I16_8), i, vv))))" +
    " && app_extract_vec(Svi(I32_4), sx, i, vv) == ConstInt32(deserialise_i32(lane_bytes(Svi(I32_4), i, vv)))" +
    " && app_extract_vec(Svi(I64_2), sx, i, vv) == ConstInt64(deserialise_i64(lane_bytes(Svi(I64_2), i, vv)))" +
    " && app_extract_vec(Svf(F32_4), sx, i, vv) == ConstFloat32(deserialise_f32(lane_bytes(Svf(F32_4), i, vv)))" +
    " && app_extract_vec(Svf(F64_2), sx, i, vv) == ConstFloat64(deserialise_f64(lane_bytes(Svf(F64_2), i, vv)))",
  )
  def(
    "app_replace_vec",
    "app_replace_vec(sv, i, vv, vn) == ConstVec128(deserialise_v128(insert_lane_vec_bs(vec_length(sv), i, bits_num(vn), bits_vec(vv))))",
  )
  def(
    "read_bytes_vec",
    "read_bytes_vec(0, len, sx, m, ind) == NIL && read_bytes_vec(SUC(n), len, sx, m, ind) == APPEND(sign_extend(sx, len * 2, read_bytes(m, ind, len)), read_bytes_vec(n, len, sx, m, ind + len))",
  )
  def(
    "load_packed_vec",
    "load_packed_vec(tp, sx, m, n, off) == (if n + off + tp_vec_num(tp) * tp_vec_length(tp) <= mem_length(m) { SOME(read_bytes_vec(tp_vec_num(tp), tp_vec_length(tp), sx, m, n + off)) } else { NONE })",
  )
  def(
    "load_vec",
    "load_vec(Load_128, m, n, off) == load(m, n, off, t_vec_length(T_v128))" +
    " && load_vec(Load_packed_vec(tp, sx), m, n, off) == load_packed_vec(tp, sx, m, n, off)" +
    " && load_vec(Load_32_zero, m, n, off) == map_option((bs : \{bytes}) => bytes_takefill(zero_byte, t_vec_length(T_v128), bs), load(m, n, off, 4))" +
    " && load_vec(Load_64_zero, m, n, off) == map_option((bs : \{bytes}) => bytes_takefill(zero_byte, t_vec_length(T_v128), bs), load(m, n, off, 8))" +
    " && load_vec(Load_splat(svi), m, n, off) == map_option((bs : \{bytes}) => concat(REPLICATE(vec_i_num(svi), bs)), load(m, n, off, vec_i_length(svi)))",
  )
  def(
    "insert_lane_vec",
    "insert_lane_vec(svi, i, bs, v) == deserialise_v128(insert_lane_vec_bs(vec_i_length(svi), i, bs, serialise_v128(v)))",
  )
  def(
    "store_serialise_vec",
    "store_serialise_vec(Store_128, v) == serialise_v128(v) && store_serialise_vec(Store_lane(svi, i), v) == take(vec_i_length(svi), drop(i * vec_i_length(svi), serialise_v128(v)))",
  )
}

///|
/// Wasm_Base_Defs: conversions (cvt) and reinterpretation.
fn define_cvt() -> Unit raise {
  fn trunc(i : String, f : String, c : String) -> String {
    "match sat_sx { SOME((Nonsat, U)) => u\{i}_trunc_\{f}(\{c}); SOME((Nonsat, S)) => s\{i}_trunc_\{f}(\{c}); SOME((Sat, U)) => SOME(u\{i}_trunc_sat_\{f}(\{c})); SOME((Sat, S)) => SOME(s\{i}_trunc_sat_\{f}(\{c})); NONE => NONE }"
  }

  fn convert(f : String, i : String, c : String) -> String {
    "match sat_sx { SOME((x1, U)) => SOME(\{f}_convert_u\{i}(\{c})); SOME((x2, S)) => SOME(\{f}_convert_s\{i}(\{c})); NONE => NONE }"
  }

  def(
    "cvt_i32",
    "cvt_i32(sat_sx, ConstInt32(c1)) == NONE" +
    " && cvt_i32(sat_sx, ConstInt64(c2)) == SOME(wasm_wrap(c2))" +
    " && cvt_i32(sat_sx, ConstFloat32(c3)) == (\{trunc("i32", "f32", "c3")})" +
    " && cvt_i32(sat_sx, ConstFloat64(c4)) == (\{trunc("i32", "f64", "c4")})",
  )
  def(
    "cvt_i64",
    "cvt_i64(sat_sx, ConstInt32(c1)) == (match sat_sx { SOME((x1, U)) => SOME(wasm_extend_u(c1)); SOME((x2, S)) => SOME(wasm_extend_s(c1)); NONE => NONE })" +
    " && cvt_i64(sat_sx, ConstInt64(c2)) == NONE" +
    " && cvt_i64(sat_sx, ConstFloat32(c3)) == (\{trunc("i64", "f32", "c3")})" +
    " && cvt_i64(sat_sx, ConstFloat64(c4)) == (\{trunc("i64", "f64", "c4")})",
  )
  def(
    "cvt_f32",
    "cvt_f32(sat_sx, ConstInt32(c1)) == (\{convert("f32", "i32", "c1")})" +
    " && cvt_f32(sat_sx, ConstInt64(c2)) == (\{convert("f32", "i64", "c2")})" +
    " && cvt_f32(sat_sx, ConstFloat32(c3)) == NONE" +
    " && cvt_f32(sat_sx, ConstFloat64(c4)) == SOME(wasm_demote(c4))",
  )
  def(
    "cvt_f64",
    "cvt_f64(sat_sx, ConstInt32(c1)) == (\{convert("f64", "i32", "c1")})" +
    " && cvt_f64(sat_sx, ConstInt64(c2)) == (\{convert("f64", "i64", "c2")})" +
    " && cvt_f64(sat_sx, ConstFloat32(c3)) == SOME(wasm_promote(c3))" +
    " && cvt_f64(sat_sx, ConstFloat64(c4)) == NONE",
  )
  def(
    "cvt",
    "cvt(T_i32, sat_sx, v) == (match cvt_i32(sat_sx, v) { SOME(c1) => SOME(ConstInt32(c1)); NONE => NONE })" +
    " && cvt(T_i64, sat_sx, v) == (match cvt_i64(sat_sx, v) { SOME(c2) => SOME(ConstInt64(c2)); NONE => NONE })" +
    " && cvt(T_f32, sat_sx, v) == (match cvt_f32(sat_sx, v) { SOME(c3) => SOME(ConstFloat32(c3)); NONE => NONE })" +
    " && cvt(T_f64, sat_sx, v) == (match cvt_f64(sat_sx, v) { SOME(c4) => SOME(ConstFloat64(c4)); NONE => NONE })",
  )
  def(
    "wasm_reinterpret",
    "wasm_reinterpret(t, v) == wasm_deserialise_num(bits_num(v), t)",
  )
}
