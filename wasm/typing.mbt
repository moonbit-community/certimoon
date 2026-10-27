// Wasm.thy, part 1: the typing relations.
//
// Isabelle's notation: C ⊢ es : tf is b_e_typing(C, es, tf);
// s•C ⊢ es : tf is e_typing(s, C, es, tf); s•rs ⊩ f;es : ts is
// thread_typing(s, rs, f, es, ts); ⊢ s;f;es : ts is config_typing.
// t1s _> t2s is Tf(t1s, t2s), and C⦇label := x⦈ is
// ctx_label_update(x, C).

///|
let i32t : String = "T_num(T_i32)"

///|
let v128t : String = "T_vec(T_v128)"

///|
/// C with label ts pushed (Isabelle: C⦇label := [ts] @ label C⦈).
fn push_label(ts : String, c : String) -> String {
  "ctx_label_update(CONS(\{ts}, ctx_label(\{c})), \{c})"
}

///|
fn define_b_e_typing() -> Unit raise {
  let mem1 = "LENGTH(ctx_memory(C)) >= 1"
  let i3 = "[\{i32t}, \{i32t}, \{i32t}]"
  inductive("b_e_typing", [("b_e_typing", "(T_context, List[B_e], Tf) -> Bool")], [
    // numeric operators
    "b_e_typing(C, [EConstNum(v)], Tf(NIL, [T_num(typeof_num(v))]))",
    "b_e_typing(C, [EConstVec(v)], Tf(NIL, [T_vec(typeof_vec(v))]))",
    "unop_t_num_agree(op, t) → b_e_typing(C, [Unop(t, op)], Tf([T_num(t)], [T_num(t)]))",
    "binop_t_num_agree(op, t) → b_e_typing(C, [Binop(t, op)], Tf([T_num(t), T_num(t)], [T_num(t)]))",
    "is_int_t_num(t) → b_e_typing(C, [Testop(t, op)], Tf([T_num(t)], [\{i32t}]))",
    "relop_t_num_agree(op, t) → b_e_typing(C, [Relop(t, op)], Tf([T_num(t), T_num(t)], [\{i32t}]))",
    // references
    "b_e_typing(C, [Ref_null(t)], Tf(NIL, [T_ref(t)]))",
    "b_e_typing(C, [Ref_is_null], Tf([T_ref(t)], [\{i32t}]))",
    "j < LENGTH(ctx_func(C)) && MEM(j, ctx_refs(C)) → b_e_typing(C, [Ref_func(j)], Tf(NIL, [T_ref(T_func_ref)]))",
    // vector operators
    "b_e_typing(C, [Unop_vec(op)], Tf([\{v128t}], [\{v128t}]))",
    "binop_vec_wf(op) → b_e_typing(C, [Binop_vec(op)], Tf([\{v128t}, \{v128t}], [\{v128t}]))",
    "b_e_typing(C, [Ternop_vec(op)], Tf([\{v128t}, \{v128t}, \{v128t}], [\{v128t}]))",
    "b_e_typing(C, [Test_vec(op)], Tf([\{v128t}], [\{i32t}]))",
    "b_e_typing(C, [Shift_vec(op)], Tf([\{v128t}, \{i32t}], [\{v128t}]))",
    "b_e_typing(C, [Splat_vec(sv)], Tf([T_num(vec_lane_t(sv))], [\{v128t}]))",
    "i < vec_num(sv) && (sx == U || vec_length(sv) <= 2) → b_e_typing(C, [Extract_vec(sv, sx, i)], Tf([\{v128t}], [T_num(vec_lane_t(sv))]))",
    "i < vec_num(sv) → b_e_typing(C, [Replace_vec(sv, i)], Tf([\{v128t}, T_num(vec_lane_t(sv))], [\{v128t}]))",
    // convert and reinterpret
    "t1 != t2 && ((sat_sx == NONE) == ((is_float_t_num(t1) && is_float_t_num(t2)) || (is_int_t_num(t1) && is_int_t_num(t2) && t_num_length(t1) < t_num_length(t2)))) → b_e_typing(C, [Cvtop(t1, Convert, t2, sat_sx)], Tf([T_num(t2)], [T_num(t1)]))",
    "t1 != t2 && t_num_length(t1) == t_num_length(t2) → b_e_typing(C, [Cvtop(t1, Reinterpret, t2, NONE)], Tf([T_num(t2)], [T_num(t1)]))",
    // unreachable, nop, drop, select
    "b_e_typing(C, [Unreachable], Tf(ts, ts'))",
    "b_e_typing(C, [Nop], Tf(NIL, NIL))",
    "b_e_typing(C, [Drop], Tf([t], NIL))",
    "(t_tag == NONE && (is_num_type(t) || is_vec_type(t) || t == T_bot)) || t_tag == SOME(t) → b_e_typing(C, [Select(t_tag)], Tf([t, t, \{i32t}], [t]))",
    // block, loop, if
    "tb_tf_t(C, tb) == SOME(Tf(tn, tm)) && b_e_typing(\{push_label("tm", "C")}, es, Tf(tn, tm)) → b_e_typing(C, [Block(tb, es)], Tf(tn, tm))",
    "tb_tf_t(C, tb) == SOME(Tf(tn, tm)) && b_e_typing(\{push_label("tn", "C")}, es, Tf(tn, tm)) → b_e_typing(C, [Loop(tb, es)], Tf(tn, tm))",
    "tb_tf_t(C, tb) == SOME(Tf(tn, tm)) && b_e_typing(\{push_label("tm", "C")}, es1, Tf(tn, tm)) && b_e_typing(\{push_label("tm", "C")}, es2, Tf(tn, tm)) → b_e_typing(C, [If(tb, es1, es2)], Tf(APPEND(tn, [\{i32t}]), tm))",
    // branches
    "i < LENGTH(ctx_label(C)) && EL(i, ctx_label(C)) == ts → b_e_typing(C, [Br(i)], Tf(APPEND(t1s, ts), t2s))",
    "i < LENGTH(ctx_label(C)) && EL(i, ctx_label(C)) == ts → b_e_typing(C, [Br_if(i)], Tf(APPEND(ts, [\{i32t}]), ts))",
    "ALL((k : Num) => k < LENGTH(ctx_label(C)) && t_list_subtyping(ts, EL(k, ctx_label(C))), APPEND(is_, [i])) → b_e_typing(C, [Br_table(is_, i)], Tf(APPEND(t1s, APPEND(ts, [\{i32t}])), t2s))",
    "ctx_return(C) == SOME(ts) → b_e_typing(C, [Return], Tf(APPEND(t1s, ts), t2s))",
    // calls
    "i < LENGTH(ctx_func(C)) && EL(i, ctx_func(C)) == tf → b_e_typing(C, [Call(i)], tf)",
    "i < LENGTH(ctx_types(C)) && EL(i, ctx_types(C)) == Tf(t1s, t2s) && ti < LENGTH(ctx_table(C)) && EL(ti, ctx_table(C)) == T_tab(lim, T_func_ref) → b_e_typing(C, [Call_indirect(ti, i)], Tf(APPEND(t1s, [\{i32t}]), t2s))",
    // locals and globals
    "i < LENGTH(ctx_local(C)) && EL(i, ctx_local(C)) == t → b_e_typing(C, [Local_get(i)], Tf(NIL, [t]))",
    "i < LENGTH(ctx_local(C)) && EL(i, ctx_local(C)) == t → b_e_typing(C, [Local_set(i)], Tf([t], NIL))",
    "i < LENGTH(ctx_local(C)) && EL(i, ctx_local(C)) == t → b_e_typing(C, [Local_tee(i)], Tf([t], [t]))",
    "i < LENGTH(ctx_global(C)) && tg_t(EL(i, ctx_global(C))) == t → b_e_typing(C, [Global_get(i)], Tf(NIL, [t]))",
    "i < LENGTH(ctx_global(C)) && tg_t(EL(i, ctx_global(C))) == t && is_mut(EL(i, ctx_global(C))) → b_e_typing(C, [Global_set(i)], Tf([t], NIL))",
    // memory
    "\{mem1} && load_store_t_bounds(a, option_projl(tp_sx), t) → b_e_typing(C, [Load(t, tp_sx, a, off)], Tf([\{i32t}], [T_num(t)]))",
    "\{mem1} && load_store_t_bounds(a, tp, t) → b_e_typing(C, [Store(t, tp, a, off)], Tf([\{i32t}, T_num(t)], NIL))",
    "\{mem1} && load_vec_t_bounds(lvop, a) → b_e_typing(C, [Load_vec(lvop, a, off)], Tf([\{i32t}], [\{v128t}]))",
    "\{mem1} && (i < vec_i_num(svi) && EXP(2, a) <= vec_i_length(svi)) → b_e_typing(C, [Load_lane_vec(svi, i, a, off)], Tf([\{i32t}, \{v128t}], [\{v128t}]))",
    "\{mem1} && store_vec_t_bounds(svop, a) → b_e_typing(C, [Store_vec(svop, a, off)], Tf([\{i32t}, \{v128t}], NIL))",
    "\{mem1} → b_e_typing(C, [Memory_size], Tf(NIL, [\{i32t}]))",
    "\{mem1} → b_e_typing(C, [Memory_grow], Tf([\{i32t}], [\{i32t}]))",
    // tables
    "ti < LENGTH(ctx_table(C)) && tab_t_reftype(EL(ti, ctx_table(C))) == tr → b_e_typing(C, [Table_set(ti)], Tf([\{i32t}, T_ref(tr)], NIL))",
    "ti < LENGTH(ctx_table(C)) && tab_t_reftype(EL(ti, ctx_table(C))) == tr → b_e_typing(C, [Table_get(ti)], Tf([\{i32t}], [T_ref(tr)]))",
    "ti < LENGTH(ctx_table(C)) → b_e_typing(C, [Table_size(ti)], Tf(NIL, [\{i32t}]))",
    "ti < LENGTH(ctx_table(C)) && tab_t_reftype(EL(ti, ctx_table(C))) == tr → b_e_typing(C, [Table_grow(ti)], Tf([T_ref(tr), \{i32t}], [\{i32t}]))",
    // empty program, composition, subsumption
    "b_e_typing(C, NIL, Tf(NIL, NIL))",
    "b_e_typing(C, es, Tf(t1s, t2s)) && b_e_typing(C, [e], Tf(t2s, t3s)) → b_e_typing(C, APPEND(es, [e]), Tf(t1s, t3s))",
    "b_e_typing(C, es, Tf(tf1, tf2)) && instr_subtyping(Tf(tf1, tf2), Tf(tf1', tf2')) → b_e_typing(C, es, Tf(tf1', tf2'))",
    // bulk memory and table operations
    "\{mem1} && i < LENGTH(ctx_data(C)) → b_e_typing(C, [Memory_init(i)], Tf(\{i3}, NIL))",
    "\{mem1} → b_e_typing(C, [Memory_copy], Tf(\{i3}, NIL))",
    "\{mem1} → b_e_typing(C, [Memory_fill], Tf(\{i3}, NIL))",
    "x < LENGTH(ctx_table(C)) && y < LENGTH(ctx_elem(C)) && tr == tab_t_reftype(EL(x, ctx_table(C))) && tr == EL(y, ctx_elem(C)) → b_e_typing(C, [Table_init(x, y)], Tf(\{i3}, NIL))",
    "x < LENGTH(ctx_table(C)) && tr == tab_t_reftype(EL(x, ctx_table(C))) && y < LENGTH(ctx_table(C)) && tr == tab_t_reftype(EL(y, ctx_table(C))) → b_e_typing(C, [Table_copy(x, y)], Tf(\{i3}, NIL))",
    "x < LENGTH(ctx_table(C)) && tr == tab_t_reftype(EL(x, ctx_table(C))) → b_e_typing(C, [Table_fill(x)], Tf([\{i32t}, T_ref(tr), \{i32t}], NIL))",
    "x < LENGTH(ctx_elem(C)) → b_e_typing(C, [Elem_drop(x)], Tf(NIL, NIL))",
    "x < LENGTH(ctx_data(C)) → b_e_typing(C, [Data_drop(x)], Tf(NIL, NIL))",
  ])
}

///|
/// Values, instances, frames and closures against the store.
fn define_store_typing_parts() -> Unit raise {
  inductive("ref_typing", [("ref_typing", "(Wstore, V_ref, T_ref) -> Bool")], [
    "ref_typing(s, ConstNull(t), t)",
    "f < LENGTH(s_funcs(s)) → ref_typing(s, ConstRefFunc(f), T_func_ref)",
    "ref_typing(s, ConstRefExtern(h), T_ext_ref)",
  ])
  inductive("v_typing", [("v_typing", "(Wstore, Value, Valtype) -> Bool")], [
    "v_typing(s, V_num(vn), T_num(typeof_num(vn)))",
    "v_typing(s, V_vec(vv), T_vec(typeof_vec(vv)))",
    "ref_typing(s, vr, t) → v_typing(s, V_ref(vr), T_ref(t))",
  ])
  def(
    "glob_typing",
    "glob_typing(g, tg) == (tg_mut(tg) == g_mut(g) && tg_t(tg) == typeof_v(g_val(g)))",
  )
  def(
    "globi_agree",
    "globi_agree(gs, n, g) == (n < LENGTH(gs) && glob_typing(EL(n, gs), g))",
  )
  def(
    "tabi_agree",
    "tabi_agree((ts : List[\{tabinst_ty}]), n, tab_t) == (n < LENGTH(ts) && tab_subtyping(FST(EL(n, ts)), tab_t))",
  )
  def(
    "memi_agree",
    "memi_agree((ms : List[\{mem_ty}]), n, mem_t) == (n < LENGTH(ms) && mem_subtyping(FST(EL(n, ms)), mem_t))",
  )
  def(
    "funci_agree",
    "funci_agree(fs, n, f) == (n < LENGTH(fs) && cl_type(EL(n, fs)) == f)",
  )
  def("data_typing", "data_typing((d : \{bytes}), (dt : Unit)) == true")
  def(
    "datai_agree",
    "datai_agree(ds, n, dt) == (n < LENGTH(ds) && data_typing(EL(n, ds), dt))",
  )
  def(
    "elem_typing",
    "elem_typing(s, (ei : \{eleminst_ty}), et) == (FST(ei) == et && ALL((vr : V_ref) => ref_typing(s, vr, et), SND(ei)))",
  )
  def(
    "elemi_agree",
    "elemi_agree(s, es, n, et) == (n < LENGTH(es) && elem_typing(s, EL(n, es), et))",
  )
  inductive("inst_typing", [("inst_typing", "(Wstore, Inst, T_context) -> Bool")], [
    "ALL2(funci_agree(s_funcs(s)), fs, tfs) && ALL2(globi_agree(s_globs(s)), gs, tgs) && ALL2(tabi_agree(s_tabs(s)), tbs, tabs_t) && ALL2(memi_agree(s_mems(s)), ms, mems_t) && ALL2(elemi_agree(s, s_elems(s)), es, elems_t) && ALL2(datai_agree(s_datas(s)), ds, datas_t)" +
    " → inst_typing(s, Inst(ts, fs, tbs, ms, gs, es, ds), T_context(ts, tfs, tgs, elems_t, datas_t, tabs_t, mems_t, NIL, NIL, NONE, upt(0, LENGTH(fs))))",
  ])
  inductive("frame_typing", [("frame_typing", "(Wstore, Wframe, T_context) -> Bool")], [
    "ALL2((v : Value) => (t : Valtype) => v_typing(s, v, t), f_locs(f), tvs) && inst_typing(s, f_inst(f), C) → frame_typing(s, f, ctx_local_update(tvs, C))",
  ])
  // n_zeros ts ≠ None: t now also has T_bot, which has no zero
  inductive("cl_typing", [("cl_typing", "(Wstore, Cl, Tf) -> Bool")], [
    "inst_typing(s, i, C) && tf == Tf(t1s, t2s) && b_e_typing(ctx_return_update(SOME(t2s), \{push_label("t2s", "ctx_local_update(APPEND(t1s, ts), C)")}), es, Tf(NIL, t2s)) && n_zeros(ts) != NONE → cl_typing(s, Func_native(i, tf, ts, es), Tf(t1s, t2s))",
    "cl_typing(s, Func_host(tf, h), tf)",
  ])
}

///|
/// The typing of administrative instructions and threads (mutually
/// inductive), and of stores and configurations.
fn define_e_typing() -> Unit raise {
  inductive(
    "e_typing",
    [
      ("e_typing", "(Wstore, T_context, List[Einstr], Tf) -> Bool"),
      (
        "thread_typing",
        "(Wstore, Option[List[Valtype]], Wframe, List[Einstr], List[Valtype]) -> Bool",
      ),
    ],
    [
      // lifting, composition, subsumption
      "b_e_typing(C, b_es, tf) → e_typing(s, C, MAP(Basic, b_es), tf)",
      "e_typing(s, C, es, Tf(t1s, t2s)) && e_typing(s, C, [e], Tf(t2s, t3s)) → e_typing(s, C, APPEND(es, [e]), Tf(t1s, t3s))",
      "e_typing(s, C, es, Tf(tf1, tf2)) && instr_subtyping(Tf(tf1, tf2), Tf(tf1', tf2')) → e_typing(s, C, es, Tf(tf1', tf2'))",
      // references, trap, frame, invoke, label
      "ref_typing(s, v_r, t) → e_typing(s, C, [Ref(v_r)], Tf(NIL, [T_ref(t)]))",
      "e_typing(s, C, [Trap], tf)",
      "thread_typing(s, SOME(ts), f, es, ts) && LENGTH(ts) == n → e_typing(s, C, [Frame(n, f, es)], Tf(NIL, ts))",
      "i < LENGTH(s_funcs(s)) && cl_type(EL(i, s_funcs(s))) == tf → e_typing(s, C, [Invoke(i)], tf)",
      "e_typing(s, C, e0s, Tf(ts, t2s)) && e_typing(s, \{push_label("ts", "C")}, es, Tf(NIL, t2s)) && LENGTH(ts) == n → e_typing(s, C, [Label(n, e0s, es)], Tf(NIL, t2s))",
      // threads
      "frame_typing(s, f, C) && e_typing(s, ctx_return_update(rs, C), es, Tf(NIL, ts)) → thread_typing(s, rs, f, es, ts)",
    ],
  )
  def(
    "glob_agree",
    "glob_agree(s, glob) == (∃ t : Valtype, v_typing(s, g_val(glob), t))",
  )
  def(
    "tab_agree",
    "tab_agree(s, (T_tab(lims, tr), tab_elems)) == (l_min(lims) == tab_size((T_tab(lims, tr), tab_elems)) && pred_option((max : Num) => tab_size((T_tab(lims, tr), tab_elems)) <= max, tab_max((T_tab(lims, tr), tab_elems))) && ALL((vr : V_ref) => ref_typing(s, vr, tr), tab_elems))",
  )
  def(
    "elem_agree",
    "elem_agree(s, (ei : \{eleminst_ty})) == ALL((vr : V_ref) => ref_typing(s, vr, FST(ei)), SND(ei))",
  )
  def("data_agree", "data_agree((s : Wstore), (di : \{bytes})) == true")
  // Isabelle: abbreviation
  def(
    "mem_agree",
    "mem_agree((m : \{mem_ty})) == (l_min(FST(m)) * Ki64 == mem_length(m) && pred_option((max : Num) => mem_size(m) <= max, mem_max(m)))",
  )
  inductive("store_typing", [("store_typing", "(Wstore) -> Bool")], [
    "ALL((cl : Cl) => ∃ tf : Tf, cl_typing(s, cl, tf), s_funcs(s)) && ALL(tab_agree(s), s_tabs(s)) && ALL(mem_agree, s_mems(s)) && ALL(glob_agree(s), s_globs(s)) && ALL(elem_agree(s), s_elems(s)) && ALL(data_agree(s), s_datas(s)) → store_typing(s)",
  ])
  inductive(
    "config_typing",
    [("config_typing", "(Wstore, Wframe, List[Einstr], List[Valtype]) -> Bool")],
    ["store_typing(s) && thread_typing(s, NONE, f, es, ts) → config_typing(s, f, es, ts)"],
  )
}
