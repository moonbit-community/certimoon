// Wasm_Subtyping and the rest of Wasm_Base_Defs: subtyping, store and
// instance lookups, store extension and evaluation contexts (Lfilled).

///|
fn define_subtyping() -> Unit raise {
  def(
    "limits_compat",
    "limits_compat(lt1, lt2) == (l_min(lt1) >= l_min(lt2) && pred_option((lt2_the : Num) => (match l_max(lt1) { SOME(lt1_the) => lt1_the <= lt2_the; NONE => false }), l_max(lt2)))",
  )
  def("t_subtyping", "t_subtyping(t1, t2) == (t1 == T_bot || t1 == t2)")
  def(
    "t_list_subtyping",
    "t_list_subtyping(t1s, t2s) == ALL2(t_subtyping, t1s, t2s)",
  )
  def(
    "instr_subtyping",
    "instr_subtyping(tf1, tf2) == (∃ ts : _, ∃ ts' : _, ∃ tf1_dom_sub : _, ∃ tf1_ran_sub : _, tf_dom(tf2) == APPEND(ts, tf1_dom_sub) && tf_ran(tf2) == APPEND(ts', tf1_ran_sub) && t_list_subtyping(ts, ts') && t_list_subtyping(tf1_dom_sub, tf_dom(tf1)) && t_list_subtyping(tf_ran(tf1), tf1_ran_sub))",
  )
  def("mem_subtyping", "mem_subtyping(t1, t2) == limits_compat(t1, t2)")
  def(
    "tab_subtyping",
    "tab_subtyping(T_tab(lims1, tr1), T_tab(lims2, tr2)) == (limits_compat(lims1, lims2) && tr1 == tr2)",
  )
}

///|
fn define_store_lookups() -> Unit raise {
  def(
    "cl_type",
    "cl_type(Func_native(i, tf1, ts, es)) == tf1 && cl_type(Func_host(tf2, h)) == tf2",
  )
  def(
    "tb_tf",
    "tb_tf(inst, Tbf(i)) == EL(i, inst_types(inst)) && tb_tf(inst, Tbv(SOME(t))) == Tf(NIL, [t]) && tb_tf(inst, Tbv(NONE)) == Tf(NIL, NIL)",
  )
  def(
    "tb_tf_t",
    "tb_tf_t(C, Tbf(i)) == (if i < LENGTH(ctx_types(C)) { SOME(EL(i, ctx_types(C))) } else { NONE }) && tb_tf_t(C, Tbv(SOME(t))) == SOME(Tf(NIL, [t])) && tb_tf_t(C, Tbv(NONE)) == SOME(Tf(NIL, NIL))",
  )
  def("rglob_is_mut", "rglob_is_mut(g) == (g_mut(g) == T_mut)")
  def("stypes", "stypes(i, j) == EL(j, inst_types(i))")
  def("sfunc_ind", "sfunc_ind(i, j) == EL(j, inst_funcs(i))")
  def("sfunc", "sfunc(s, i, j) == EL(sfunc_ind(i, j), s_funcs(s))")
  def("sglob_ind", "sglob_ind(i, j) == EL(j, inst_globs(i))")
  def("sglob", "sglob(s, i, j) == EL(sglob_ind(i, j), s_globs(s))")
  def("sglob_val", "sglob_val(s, i, j) == g_val(sglob(s, i, j))")
  def(
    "smem_ind",
    "smem_ind(i) == (match inst_mems(i) { CONS(n, rest) => SOME(n); NIL => NONE })",
  )
  def(
    "tab_cl_ind",
    "tab_cl_ind((st : List[\{tabinst_ty}]), i, j) == (if LENGTH(SND(EL(i, st))) > j { SOME(EL(j, SND(EL(i, st)))) } else { NONE })",
  )
  def(
    "is_some_const_ref_func",
    "is_some_const_ref_func(x) == (match x { SOME(ConstRefFunc(i)) => true; other => false })",
  )
  def("stab_cl_ind", "stab_cl_ind(s, i, j) == tab_cl_ind(s_tabs(s), i, j)")
  def(
    "stab",
    "stab(s, i, ti, j) == (if ti < LENGTH(inst_tabs(i)) { stab_cl_ind(s, EL(ti, inst_tabs(i)), j) } else { NONE })",
  )
  def(
    "stab_ind",
    "stab_ind(i, ti) == (if ti < LENGTH(inst_tabs(i)) { SOME(EL(ti, inst_tabs(i))) } else { NONE })",
  )
  def(
    "update_glob",
    "update_glob(gs, i, j, v) == list_update(gs, sglob_ind(i, j), g_val_update(v, EL(sglob_ind(i, j), gs)))",
  )
  def(
    "supdate_glob",
    "supdate_glob(s, i, j, v) == s_globs_update(update_glob(s_globs(s), i, j, v), s)",
  )
  def(
    "is_const",
    "is_const(e) == (match e { Basic(EConstNum(x)) => true; Basic(EConstVec(y)) => true; Ref(z) => true; other => false })",
  )
  def("const_list", "const_list(xs) == ALL(is_const, xs)")
}

///|
fn define_extension() -> Unit raise {
  def(
    "tab_extension",
    "tab_extension(t1, t2) == (tab_size(t1) <= tab_size(t2) && tab_max(t1) == tab_max(t2) && tab_subtyping(FST(t2), FST(t1)))",
  )
  def(
    "mem_extension",
    "mem_extension(m1, m2) == (mem_size(m1) <= mem_size(m2) && mem_max(m1) == mem_max(m2) && mem_subtyping(FST(m2), FST(m1)))",
  )
  def(
    "global_extension",
    "global_extension(g1, g2) == (g_mut(g1) == g_mut(g2) && typeof_v(g_val(g1)) == typeof_v(g_val(g2)) && (g_mut(g1) == T_immut → g_val(g1) == g_val(g2)))",
  )
  def(
    "elem_extension",
    "elem_extension((e1 : \{eleminst_ty}), e2) == (FST(e1) == FST(e2) && (SND(e1) == SND(e2) || LENGTH(SND(e2)) == 0))",
  )
  def(
    "data_extension",
    "data_extension((d1 : \{bytes}), d2) == (d1 == d2 || LENGTH(d2) == 0)",
  )
  inductive("store_extension", [("store_extension", "(Wstore, Wstore) -> Bool")], [
    "fs == fs' && ALL2(tab_extension, tclss, tclss') && ALL2(mem_extension, bss, bss') && ALL2(global_extension, gs, gs') && ALL2(elem_extension, es, es') && ALL2(data_extension, ds, ds')" +
    " → store_extension(Wstore(fs, tclss, bss, gs, es, ds), Wstore(APPEND(fs', fs''), APPEND(tclss', tclss''), APPEND(bss', bss''), APPEND(gs', gs''), APPEND(es', es''), APPEND(ds', dss'')))",
  ])
}

///|
/// Values as instructions, and evaluation contexts.
fn define_contexts() -> Unit raise {
  // Isabelle writes v_to_e v as $C v, and map v_to_e vs as $C* vs
  def(
    "v_to_e",
    "v_to_e(V_num(x)) == Basic(EConstNum(x)) && v_to_e(V_vec(y)) == Basic(EConstVec(y)) && v_to_e(V_ref(r)) == Ref(r)",
  )
  // Lfilled depth context filling result
  inductive(
    "Lfilled",
    [("Lfilled", "(Num, Lholed, List[Einstr], List[Einstr]) -> Bool")],
    [
      "lholed == LBase(vs, es') → Lfilled(0, lholed, es, APPEND(MAP(v_to_e, vs), APPEND(es, es')))",
      "lholed == LRec(vs, n, es', l, es'') && Lfilled(k, l, es, lfilledk) → Lfilled(k + 1, lholed, es, APPEND(MAP(v_to_e, vs), APPEND([Label(n, es', lfilledk)], es'')))",
    ],
  )
  inductive(
    "Lfilled_exact",
    [("Lfilled_exact", "(Num, Lholed, List[Einstr], List[Einstr]) -> Bool")],
    [
      "lholed == LBase(NIL, NIL) → Lfilled_exact(0, lholed, es, es)",
      "lholed == LRec(vs, n, es', l, es'') && Lfilled_exact(k, l, es, lfilledk) → Lfilled_exact(k + 1, lholed, es, APPEND(MAP(v_to_e, vs), APPEND([Label(n, es', lfilledk)], es'')))",
    ],
  )
}

///|
/// The alignment bounds of memory instructions.
fn define_bounds() -> Unit raise {
  def(
    "load_store_t_bounds",
    "load_store_t_bounds(a, NONE, t) == (EXP(2, a) <= t_num_length(t)) && load_store_t_bounds(a, SOME(tp), t) == (EXP(2, a) <= tp_num_length(tp) && tp_num_length(tp) < t_num_length(t) && is_int_t_num(t))",
  )
  def(
    "load_vec_t_bounds",
    "load_vec_t_bounds(Load_packed_vec(tp, sx), a) == (EXP(2, a) <= tp_vec_length(tp) * tp_vec_num(tp))" +
    " && load_vec_t_bounds(Load_splat(svi), a) == (EXP(2, a) <= vec_i_length(svi))" +
    " && load_vec_t_bounds(Load_128, a) == (EXP(2, a) <= t_vec_length(T_v128))" +
    " && load_vec_t_bounds(Load_32_zero, a) == (EXP(2, a) <= t_vec_length(T_v128))" +
    " && load_vec_t_bounds(Load_64_zero, a) == (EXP(2, a) <= t_vec_length(T_v128))",
  )
  def(
    "store_vec_t_bounds",
    "store_vec_t_bounds(Store_lane(svi, i), a) == (i < vec_i_num(svi) && EXP(2, a) <= vec_i_length(svi)) && store_vec_t_bounds(Store_128, a) == (EXP(2, a) <= t_vec_length(T_v128))",
  )
}
