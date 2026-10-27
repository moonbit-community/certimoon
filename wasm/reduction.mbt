// Wasm.thy, part 2: the reduction relations.
//
// Isabelle's ⦇es⦈ ↝ ⦇es'⦈ is reduce_simple(es, es'), and
// ⦇s;f;es⦈ ↝ ⦇s';f';es'⦈ is reduce(s, f, es, s', f', es'). $b is
// Basic(b), $C v is v_to_e(v), $C* vs is MAP(v_to_e, vs) and $* bs is
// MAP(Basic, bs). Isabelle's int_eq n 0 is n == word(0), nat_of_int is
// val and int_of_nat is word.

///|
/// $EConstNum (ConstInt32 x)
fn i32c(x : String) -> String {
  "Basic(EConstNum(ConstInt32(\{x})))"
}

///|
/// $EConstNum (ConstInt32 (int_of_nat n))
fn i32n(n : String) -> String {
  i32c("word(\{n})")
}

///|
fn define_reduce_simple() -> Unit raise {
  let vs = "MAP(v_to_e, vs)"
  inductive(
    "reduce_simple",
    [("reduce_simple", "(List[Einstr], List[Einstr]) -> Bool")],
    [
      // numeric operators
      "reduce_simple([Basic(EConstNum(v)), Basic(Unop(t, op))], [Basic(EConstNum(app_unop(op, v)))])",
      "app_binop(op, v1, v2) == SOME(v) → reduce_simple([Basic(EConstNum(v1)), Basic(EConstNum(v2)), Basic(Binop(t, op))], [Basic(EConstNum(v))])",
      "app_binop(op, v1, v2) == NONE → reduce_simple([Basic(EConstNum(v1)), Basic(EConstNum(v2)), Basic(Binop(t, op))], [Trap])",
      "reduce_simple([Basic(EConstNum(v)), Basic(Testop(t, op))], [Basic(EConstNum(app_testop(op, v)))])",
      "reduce_simple([Basic(EConstNum(v1)), Basic(EConstNum(v2)), Basic(Relop(t, op))], [Basic(EConstNum(app_relop(op, v1, v2)))])",
      "typeof_num(v) == t1 && cvt(t2, sat_sx, v) == SOME(v') → reduce_simple([Basic(EConstNum(v)), Basic(Cvtop(t2, Convert, t1, sat_sx))], [Basic(EConstNum(v'))])",
      "typeof_num(v) == t1 && cvt(t2, sat_sx, v) == NONE → reduce_simple([Basic(EConstNum(v)), Basic(Cvtop(t2, Convert, t1, sat_sx))], [Trap])",
      "typeof_num(v) == t1 → reduce_simple([Basic(EConstNum(v)), Basic(Cvtop(t2, Reinterpret, t1, NONE))], [Basic(EConstNum(wasm_reinterpret(t2, v)))])",
      // references
      "reduce_simple([Basic(Ref_null(t))], [Ref(ConstNull(t))])",
      "is_null_ref(v_r) → reduce_simple([Ref(v_r), Basic(Ref_is_null)], [\{i32c("wasm_bool(true)")}])",
      "!is_null_ref(v_r) → reduce_simple([Ref(v_r), Basic(Ref_is_null)], [\{i32c("wasm_bool(false)")}])",
      // vector operators
      "reduce_simple([Basic(EConstVec(v)), Basic(Unop_vec(op))], [Basic(EConstVec(app_unop_vec(op, v)))])",
      "app_binop_vec(op, v1, v2) == SOME(v) → reduce_simple([Basic(EConstVec(v1)), Basic(EConstVec(v2)), Basic(Binop_vec(op))], [Basic(EConstVec(v))])",
      "app_binop_vec(op, v1, v2) == NONE → reduce_simple([Basic(EConstVec(v1)), Basic(EConstVec(v2)), Basic(Binop_vec(op))], [Trap])",
      "reduce_simple([Basic(EConstVec(v1)), Basic(EConstVec(v2)), Basic(EConstVec(v3)), Basic(Ternop_vec(op))], [Basic(EConstVec(app_ternop_vec(op, v1, v2, v3)))])",
      "reduce_simple([Basic(EConstVec(v)), Basic(Test_vec(op))], [\{i32c("app_test_vec(op, v)")}])",
      "reduce_simple([Basic(EConstVec(v)), \{i32c("n")}, Basic(Shift_vec(op))], [Basic(EConstVec(app_shift_vec(op, v, n)))])",
      "reduce_simple([Basic(EConstNum(v)), Basic(Splat_vec(sv))], [Basic(EConstVec(app_splat_vec(sv, v)))])",
      "reduce_simple([Basic(EConstVec(v)), Basic(Extract_vec(sv, sx, i))], [Basic(EConstNum(app_extract_vec(sv, sx, i, v)))])",
      "reduce_simple([Basic(EConstVec(v)), Basic(EConstNum(vn)), Basic(Replace_vec(sv, i))], [Basic(EConstVec(app_replace_vec(sv, i, v, vn)))])",
      // unreachable, nop, drop, select
      "reduce_simple([Basic(Unreachable)], [Trap])",
      "reduce_simple([Basic(Nop)], NIL)",
      "reduce_simple([v_to_e(v), Basic(Drop)], NIL)",
      "n == word(0) → reduce_simple([v_to_e(v1), v_to_e(v2), \{i32c("n")}, Basic(Select(t_tag))], [v_to_e(v2)])",
      "n != word(0) → reduce_simple([v_to_e(v1), v_to_e(v2), \{i32c("n")}, Basic(Select(t_tag))], [v_to_e(v1)])",
      // if
      "n == word(0) → reduce_simple([\{i32c("n")}, Basic(If(tb, e1s, e2s))], [Basic(Block(tb, e2s))])",
      "n != word(0) → reduce_simple([\{i32c("n")}, Basic(If(tb, e1s, e2s))], [Basic(Block(tb, e1s))])",
      // label
      "reduce_simple([Label(n, es, \{vs})], \{vs})",
      "reduce_simple([Label(n, es, [Trap])], [Trap])",
      // br, br_if, br_table
      "LENGTH(vs) == n && Lfilled(i, lholed, APPEND(\{vs}, [Basic(Br(i))]), LI) → reduce_simple([Label(n, es, LI)], APPEND(\{vs}, es))",
      "n == word(0) → reduce_simple([\{i32c("n")}, Basic(Br_if(i))], NIL)",
      "n != word(0) → reduce_simple([\{i32c("n")}, Basic(Br_if(i))], [Basic(Br(i))])",
      "LENGTH(is_) > val(c) → reduce_simple([\{i32c("c")}, Basic(Br_table(is_, i))], [Basic(Br(EL(val(c), is_)))])",
      "LENGTH(is_) <= val(c) → reduce_simple([\{i32c("c")}, Basic(Br_table(is_, i))], [Basic(Br(i))])",
      // local
      "reduce_simple([Frame(n, f, \{vs})], \{vs})",
      "reduce_simple([Frame(n, f, [Trap])], [Trap])",
      // return
      "LENGTH(vs) == n && Lfilled(j, lholed, APPEND(\{vs}, [Basic(Return)]), es) → reduce_simple([Frame(n, f, es)], \{vs})",
      // local_tee
      "reduce_simple([v_to_e(v), Basic(Local_tee(i))], [v_to_e(v), v_to_e(v), Basic(Local_set(i))])",
      // trap
      "es != [Trap] && Lfilled(0, lholed, [Trap], es) → reduce_simple(es, [Trap])",
    ],
  )
}

///|
fn define_reduce() -> Unit raise {
  let vs = "MAP(v_to_e, vs)"
  // the current memory: smem_ind (f_inst f) = Some j; (mems s)!j = m
  let mem = "smem_ind(f_inst(f)) == SOME(j) && EL(j, s_mems(s)) == m"
  let mem_a = "smem_ind(f_inst(f)) == SOME(ma) && EL(ma, s_mems(s)) == m"
  let set_mem = "s_mems_update(list_update(s_mems(s), j, mem'), s)"
  let k = i32c("k")
  // the three i32 operands of the bulk operations
  let three = "\{i32c("dest")}, \{i32c("src")}, \{i32c("n")}"
  let st8 = "Basic(Store(T_i32, SOME(Tp_i8), 0, 0))"
  let ld8 = "Basic(Load(T_i32, SOME((Tp_i8, U)), 0, 0))"
  let init_pre = "smem_ind(f_inst(f)) == SOME(ma) && EL(ma, s_mems(s)) == m && da == EL(x, inst_datas(f_inst(f))) && dat == EL(da, s_datas(s)) && ndest == val(dest) && nsrc == val(src) && nn == val(n)"
  let copy_pre = "\{mem_a} && ndest == val(dest) && nsrc == val(src) && nn == val(n)"
  let fill_pre = "\{mem_a} && ndest == val(dest) && nn == val(n)"
  let fill = "\{i32c("dest")}, \{i32c("fv")}, \{i32c("n")}"
  let tinit_pre = "stab_ind(f_inst(f), x) == SOME(ta) && EL(ta, s_tabs(s)) == tab && ea == EL(y, inst_elems(f_inst(f))) && el == EL(ea, s_elems(s)) && ndest == val(dest) && nsrc == val(src) && nn == val(n)"
  let tfill_pre = "stab_ind(f_inst(f), x) == SOME(ta) && EL(ta, s_tabs(s)) == tab && ni == val(i) && nn == val(n)"
  let tfill = "\{i32c("i")}, v_to_e(V_ref(vr)), \{i32c("n")}"
  // As upstream: table_copy's premises read (tabs s)!ty, where ty is not
  // bound to anything, and bind nrsc while testing nsrc, which is then
  // unconstrained.
  let tcopy_pre = "stab_ind(f_inst(f), x) == SOME(tax) && EL(tax, s_tabs(s)) == tabx && stab_ind(f_inst(f), y) == SOME(tay) && EL(ty, s_tabs(s)) == taby && ndest == val(dest) && nrsc == val(src) && nn == val(n)"
  inductive(
    "reduce",
    [("reduce", "(Wstore, Wframe, List[Einstr], Wstore, Wframe, List[Einstr]) -> Bool")],
    [
      // lifting basic reduction
      "reduce_simple(e, e') → reduce(s, f, e, s, f, e')",
      // calls
      "reduce(s, f, [Basic(Call(j))], s, f, [Invoke(sfunc_ind(f_inst(f), j))])",
      "f_inst(f) == i && stab(s, i, ti, val(c)) == SOME(ConstRefFunc(i_cl)) && stypes(i, j) == tf && cl_type(EL(i_cl, s_funcs(s))) == tf → reduce(s, f, [\{i32c("c")}, Basic(Call_indirect(ti, j))], s, f, [Invoke(i_cl)])",
      "f_inst(f) == i && ((stab(s, i, ti, val(c)) == SOME(ConstRefFunc(i_cl)) && stypes(i, j) != cl_type(EL(i_cl, s_funcs(s)))) || !is_some_const_ref_func(stab(s, i, ti, val(c)))) → reduce(s, f, [\{i32c("c")}, Basic(Call_indirect(ti, j))], s, f, [Trap])",
      // invoke
      "EL(i_cl, s_funcs(s)) == Func_native(j, Tf(t1s, t2s), ts, es) && ves == MAP(v_to_e, vcs) && LENGTH(vcs) == n && LENGTH(ts) == k && LENGTH(t1s) == n && LENGTH(t2s) == m && n_zeros(ts) == SOME(zs) → reduce(s, f, APPEND(ves, [Invoke(i_cl)]), s, f, [Frame(m, Wframe(APPEND(vcs, zs), j), [Label(m, NIL, MAP(Basic, es))])])",
      "EL(i_cl, s_funcs(s)) == Func_host(Tf(t1s, t2s), Host_func(hf)) && ves == MAP(v_to_e, vcs) && LENGTH(vcs) == n && LENGTH(t1s) == n && LENGTH(t2s) == m && host_func_apply(s, Tf(t1s, t2s), hf, vcs, hs, SOME((s', vcs'))) → reduce(s, f, APPEND(ves, [Invoke(i_cl)]), s', f, MAP(v_to_e, vcs'))",
      "EL(i_cl, s_funcs(s)) == Func_host(Tf(t1s, t2s), h) && ves == MAP(v_to_e, vcs) && LENGTH(vcs) == n && LENGTH(t1s) == n && LENGTH(t2s) == m → reduce(s, f, APPEND(ves, [Invoke(i_cl)]), s, f, [Trap])",
      // references
      "fa == EL(j, inst_funcs(f_inst(f))) → reduce(s, f, [Basic(Ref_func(j))], s, f, [Ref(ConstRefFunc(fa))])",
      // locals and globals
      "LENGTH(vi) == j && f_locs(f) == APPEND(vi, APPEND([v], vs)) → reduce(s, f, [Basic(Local_get(j))], s, f, [v_to_e(v)])",
      "LENGTH(vi) == j → reduce(s, Wframe(APPEND(vi, APPEND([v], vs)), i), [v_to_e(v'), Basic(Local_set(j))], s, Wframe(APPEND(vi, APPEND([v'], vs)), i), NIL)",
      "reduce(s, f, [Basic(Global_get(j))], s, f, [v_to_e(sglob_val(s, f_inst(f), j))])",
      "supdate_glob(s, f_inst(f), j, v) == s' → reduce(s, f, [v_to_e(v), Basic(Global_set(j))], s', f, NIL)",
      // load and store
      "\{mem} && load(m, val(k), off, t_num_length(t)) == SOME(bs) → reduce(s, f, [\{k}, Basic(Load(t, NONE, a, off))], s, f, [Basic(EConstNum(wasm_deserialise_num(bs, t)))])",
      "\{mem} && load(m, val(k), off, t_num_length(t)) == NONE → reduce(s, f, [\{k}, Basic(Load(t, NONE, a, off))], s, f, [Trap])",
      "\{mem} && load_packed(sx, m, val(k), off, tp_num_length(tp), t_num_length(t)) == SOME(bs) → reduce(s, f, [\{k}, Basic(Load(t, SOME((tp, sx)), a, off))], s, f, [Basic(EConstNum(wasm_deserialise_num(bs, t)))])",
      "\{mem} && load_packed(sx, m, val(k), off, tp_num_length(tp), t_num_length(t)) == NONE → reduce(s, f, [\{k}, Basic(Load(t, SOME((tp, sx)), a, off))], s, f, [Trap])",
      "typeof_num(v) == t && \{mem} && store(m, val(k), off, bits_num(v), t_num_length(t)) == SOME(mem') → reduce(s, f, [\{k}, Basic(EConstNum(v)), Basic(Store(t, NONE, a, off))], \{set_mem}, f, NIL)",
      "typeof_num(v) == t && \{mem} && store(m, val(k), off, bits_num(v), t_num_length(t)) == NONE → reduce(s, f, [\{k}, Basic(EConstNum(v)), Basic(Store(t, NONE, a, off))], s, f, [Trap])",
      "typeof_num(v) == t && \{mem} && store_packed(m, val(k), off, bits_num(v), tp_num_length(tp)) == SOME(mem') → reduce(s, f, [\{k}, Basic(EConstNum(v)), Basic(Store(t, SOME(tp), a, off))], \{set_mem}, f, NIL)",
      "typeof_num(v) == t && \{mem} && store_packed(m, val(k), off, bits_num(v), tp_num_length(tp)) == NONE → reduce(s, f, [\{k}, Basic(EConstNum(v)), Basic(Store(t, SOME(tp), a, off))], s, f, [Trap])",
      // vector load and store
      "\{mem} && load_vec(lv, m, val(k), off) == SOME(bs) → reduce(s, f, [\{k}, Basic(Load_vec(lv, a, off))], s, f, [Basic(EConstVec(ConstVec128(deserialise_v128(bs))))])",
      "\{mem} && load_vec(lv, m, val(k), off) == NONE → reduce(s, f, [\{k}, Basic(Load_vec(lv, a, off))], s, f, [Trap])",
      "\{mem} && load(m, val(k), off, vec_i_length(svi)) == SOME(bs) → reduce(s, f, [\{k}, Basic(EConstVec(ConstVec128(v))), Basic(Load_lane_vec(svi, i, a, off))], s, f, [Basic(EConstVec(ConstVec128(insert_lane_vec(svi, i, bs, v))))])",
      "\{mem} && load(m, val(k), off, vec_i_length(svi)) == NONE → reduce(s, f, [\{k}, Basic(EConstVec(ConstVec128(v))), Basic(Load_lane_vec(svi, i, a, off))], s, f, [Trap])",
      "\{mem} && store_serialise_vec(sv, v) == bs && store(m, val(k), off, bs, LENGTH(bs)) == SOME(mem') → reduce(s, f, [\{k}, Basic(EConstVec(ConstVec128(v))), Basic(Store_vec(sv, a, off))], \{set_mem}, f, NIL)",
      "\{mem} && store_serialise_vec(sv, v) == bs && store(m, val(k), off, bs, LENGTH(bs)) == NONE → reduce(s, f, [\{k}, Basic(EConstVec(ConstVec128(v))), Basic(Store_vec(sv, a, off))], s, f, [Trap])",
      // memory size and grow
      "\{mem} && mem_size(m) == n → reduce(s, f, [Basic(Memory_size)], s, f, [\{i32n("n")}])",
      "\{mem} && mem_size(m) == n && mem_grow(m, val(c)) == SOME(mem') → reduce(s, f, [\{i32c("c")}, Basic(Memory_grow)], \{set_mem}, f, [\{i32n("n")}])",
      "\{mem} && mem_size(m) == n → reduce(s, f, [\{i32c("c")}, Basic(Memory_grow)], s, f, [\{i32c("int32_minus_one")}])",
      // tables
      "stab_ind(f_inst(f), ti) == SOME(a) && load_tabs1(s_tabs(s), a, val(n)) == SOME(tv) → reduce(s, f, [\{i32c("n")}, Basic(Table_get(ti))], s, f, [Ref(tv)])",
      "stab_ind(f_inst(f), ti) == SOME(a) && load_tabs1(s_tabs(s), a, val(n)) == NONE → reduce(s, f, [\{i32c("n")}, Basic(Table_get(ti))], s, f, [Trap])",
      "stab_ind(f_inst(f), ti) == SOME(a) && store_tabs1(s_tabs(s), a, val(n), vr) == SOME(tabs') → reduce(s, f, [\{i32c("n")}, Ref(vr), Basic(Table_set(ti))], s_tabs_update(tabs', s), f, NIL)",
      "stab_ind(f_inst(f), ti) == SOME(a) && store_tabs1(s_tabs(s), a, val(n), vr) == NONE → reduce(s, f, [\{i32c("n")}, Ref(vr), Basic(Table_set(ti))], s, f, [Trap])",
      "stab_ind(f_inst(f), ti) == SOME(a) && EL(a, s_tabs(s)) == t && tab_size(t) == n → reduce(s, f, [Basic(Table_size(ti))], s, f, [\{i32n("n")}])",
      "stab_ind(f_inst(f), ti) == SOME(a) && EL(a, s_tabs(s)) == tab && sz == tab_size(tab) && grow_tab(tab, val(n), vr) == SOME(tab') → reduce(s, f, [Ref(vr), \{i32c("n")}, Basic(Table_grow(ti))], s_tabs_update(list_update(s_tabs(s), a, tab'), s), f, [\{i32n("sz")}])",
      "reduce(s, f, [Ref(vr), \{i32c("n")}, Basic(Table_grow(ti))], s, f, [\{i32c("int32_minus_one")}])",
      // block and loop
      "LENGTH(vs) == n && tb_tf(f_inst(f), tb) == Tf(t1s, t2s) && LENGTH(t1s) == n && LENGTH(t2s) == m → reduce(s, f, APPEND(\{vs}, [Basic(Block(tb, es))]), s, f, [Label(m, NIL, APPEND(\{vs}, MAP(Basic, es)))])",
      "LENGTH(vs) == n && tb_tf(f_inst(f), tb) == Tf(t1s, t2s) && LENGTH(t1s) == n && LENGTH(t2s) == m → reduce(s, f, APPEND(\{vs}, [Basic(Loop(tb, es))]), s, f, [Label(n, [Basic(Loop(tb, es))], APPEND(\{vs}, MAP(Basic, es)))])",
      // reduction inside a label context and inside a frame
      "reduce(s, f, es, s', f', es') && Lfilled(k, lholed, es, les) && Lfilled(k, lholed, es', les') → reduce(s, f, les, s', f', les')",
      "reduce(s, f, es, s', f', es') → reduce(s, f0, [Frame(n, f, es)], s', f0, [Frame(n, f', es')])",
      // memory.init
      "\{init_pre} && (nsrc + nn > LENGTH(dat) || ndest + nn > mem_length(m)) → reduce(s, f, [\{three}, Basic(Memory_init(x))], s, f, [Trap])",
      "\{init_pre} && nsrc + nn <= LENGTH(dat) && ndest + nn <= mem_length(m) && nn == 0 → reduce(s, f, [\{three}, Basic(Memory_init(x))], s, f, NIL)",
      "\{init_pre} && nsrc + nn <= LENGTH(dat) && ndest + nn <= mem_length(m) && nn == nn_pred + 1 && b == val(EL(nsrc, dat)) → reduce(s, f, [\{three}, Basic(Memory_init(x))], s, f, [\{i32n("ndest")}, \{i32n("b")}, \{st8}, \{i32n("ndest + 1")}, \{i32n("nsrc + 1")}, \{i32n("nn_pred")}, Basic(Memory_init(x))])",
      // memory.copy
      "\{copy_pre} && (nsrc + nn > mem_length(m) || ndest + nn > mem_length(m)) → reduce(s, f, [\{three}, Basic(Memory_copy)], s, f, [Trap])",
      "\{copy_pre} && nsrc + nn <= mem_length(m) && ndest + nn <= mem_length(m) && nn == 0 → reduce(s, f, [\{three}, Basic(Memory_copy)], s, f, NIL)",
      "\{copy_pre} && nsrc + nn <= mem_length(m) && ndest + nn <= mem_length(m) && nn == nn_pred + 1 && ndest <= nsrc → reduce(s, f, [\{three}, Basic(Memory_copy)], s, f, [\{i32c("dest")}, \{i32c("src")}, \{ld8}, \{st8}, \{i32n("ndest + 1")}, \{i32n("nsrc + 1")}, \{i32n("nn_pred")}, Basic(Memory_copy)])",
      "\{copy_pre} && nsrc + nn <= mem_length(m) && ndest + nn <= mem_length(m) && nn == nn_pred + 1 && ndest > nsrc → reduce(s, f, [\{three}, Basic(Memory_copy)], s, f, [\{i32n("ndest + nn_pred")}, \{i32n("nsrc + nn_pred")}, \{ld8}, \{st8}, \{i32c("dest")}, \{i32c("src")}, \{i32n("nn_pred")}, Basic(Memory_copy)])",
      // memory.fill
      "\{fill_pre} && ndest + nn > mem_length(m) → reduce(s, f, [\{fill}, Basic(Memory_fill)], s, f, [Trap])",
      "\{fill_pre} && ndest + nn <= mem_length(m) && nn == 0 → reduce(s, f, [\{fill}, Basic(Memory_fill)], s, f, NIL)",
      "\{fill_pre} && ndest + nn <= mem_length(m) && nn == nn_pred + 1 → reduce(s, f, [\{fill}, Basic(Memory_fill)], s, f, [\{i32c("dest")}, \{i32c("fv")}, \{st8}, \{i32n("ndest + 1")}, \{i32c("fv")}, \{i32n("nn_pred")}, Basic(Memory_fill)])",
      // table.init
      "\{tinit_pre} && (nsrc + nn > LENGTH(SND(el)) || ndest + nn > LENGTH(SND(tab))) → reduce(s, f, [\{three}, Basic(Table_init(x, y))], s, f, [Trap])",
      "\{tinit_pre} && nsrc + nn <= LENGTH(SND(el)) && ndest + nn <= LENGTH(SND(tab)) && nn == 0 → reduce(s, f, [\{three}, Basic(Table_init(x, y))], s, f, NIL)",
      "\{tinit_pre} && nsrc + nn <= LENGTH(SND(el)) && ndest + nn <= LENGTH(SND(tab)) && nn == nn_pred + 1 && tv == EL(nsrc, SND(el)) → reduce(s, f, [\{three}, Basic(Table_init(x, y))], s, f, [\{i32c("dest")}, v_to_e(V_ref(tv)), Basic(Table_set(x)), \{i32n("ndest + 1")}, \{i32n("nsrc + 1")}, \{i32n("nn_pred")}, Basic(Table_init(x, y))])",
      // table.fill
      "\{tfill_pre} && ni + nn > LENGTH(SND(tab)) → reduce(s, f, [\{tfill}, Basic(Table_fill(x))], s, f, [Trap])",
      "\{tfill_pre} && ni + nn <= LENGTH(SND(tab)) && nn == 0 → reduce(s, f, [\{tfill}, Basic(Table_fill(x))], s, f, NIL)",
      "\{tfill_pre} && ni + nn <= LENGTH(SND(tab)) && nn == nn_pred + 1 → reduce(s, f, [\{tfill}, Basic(Table_fill(x))], s, f, [\{i32c("i")}, v_to_e(V_ref(vr)), Basic(Table_set(x)), \{i32n("ni + 1")}, v_to_e(V_ref(vr)), \{i32n("nn_pred")}, Basic(Table_fill(x))])",
      // table.copy
      "\{tcopy_pre} && (nsrc + nn > LENGTH(SND(tabx)) || ndest + nn > LENGTH(SND(taby))) → reduce(s, f, [\{three}, Basic(Table_copy(x, y))], s, f, [Trap])",
      "\{tcopy_pre} && nsrc + nn <= LENGTH(SND(tabx)) && ndest + nn <= LENGTH(SND(taby)) && nn == 0 → reduce(s, f, [\{three}, Basic(Table_copy(x, y))], s, f, NIL)",
      "\{tcopy_pre} && nsrc + nn <= LENGTH(SND(tabx)) && ndest + nn <= LENGTH(SND(taby)) && nn == nn_pred + 1 && ndest <= nsrc → reduce(s, f, [\{three}, Basic(Table_copy(x, y))], s, f, [\{i32c("dest")}, \{i32c("src")}, Basic(Table_get(y)), Basic(Table_set(x)), \{i32n("ndest + 1")}, \{i32n("nsrc + 1")}, \{i32n("nn_pred")}, Basic(Table_copy(x, y))])",
      "\{tcopy_pre} && nsrc + nn <= LENGTH(SND(tabx)) && ndest + nn <= LENGTH(SND(taby)) && nn == nn_pred + 1 && ndest > nsrc → reduce(s, f, [\{three}, Basic(Table_copy(x, y))], s, f, [\{i32n("ndest + nn_pred")}, \{i32n("nsrc + nn_pred")}, Basic(Table_get(y)), Basic(Table_set(x)), \{i32c("dest")}, \{i32c("src")}, \{i32n("nn_pred")}, Basic(Table_copy(x, y))])",
      // elem.drop and data.drop
      "a == EL(x, inst_elems(f_inst(f))) → reduce(s, f, [Basic(Elem_drop(x))], s_elems_update(list_update(s_elems(s), a, (FST(EL(a, s_elems(s))), NIL)), s), f, NIL)",
      "a == EL(x, inst_datas(f_inst(f))) → reduce(s, f, [Basic(Data_drop(x))], s_datas_update(list_update(s_datas(s), a, NIL), s), f, NIL)",
    ],
  )
}

///|
/// Reflexive-transitive closure of reduce on configurations, and what a
/// configuration computes.
fn define_reduce_trans() -> Unit raise {
  let cfg = "(Wstore, Wframe, List[Einstr])"
  // Isabelle: (λ(s,f,es) (s',f',es'). ⦇s;f;es⦈ ↝ ⦇s';f';es'⦈)^**
  inductive("reduce_trans", [("reduce_trans", "(\{cfg}, \{cfg}) -> Bool")], [
    "reduce_trans(c, c)",
    "reduce(s, f, es, s', f', es') && reduce_trans((s', f', es'), c) → reduce_trans((s, f, es), c)",
  ])
  // ...^++
  inductive("reduce_irrtrans", [("reduce_irrtrans", "(\{cfg}, \{cfg}) -> Bool")], [
    "reduce(s, f, es, s', f', es') → reduce_irrtrans((s, f, es), (s', f', es'))",
    "reduce(s, f, es, s', f', es') && reduce_irrtrans((s', f', es'), c) → reduce_irrtrans((s, f, es), c)",
  ])
  def("v_stack_to_es", "v_stack_to_es(v) == MAP(v_to_e, REVERSE(v))")
  def(
    "computes",
    "computes(cfg, s', vs) == (∃ f' : Wframe, reduce_trans(cfg, (s', f', v_stack_to_es(vs))))",
  )
  def(
    "traps",
    "traps(cfg, s') == (∃ f' : Wframe, reduce_trans(cfg, (s', f', [Trap])))",
  )
  def(
    "empty_frame",
    "empty_frame == Wframe(NIL, Inst(NIL, NIL, NIL, NIL, NIL, NIL, NIL))",
  )
  def(
    "invoke_config",
    "invoke_config(s, vargs, i) == (s, empty_frame, APPEND(MAP(v_to_e, vargs), [Invoke(i)]))",
  )
}
