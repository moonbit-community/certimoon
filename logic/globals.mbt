// Rules for global.get and global.set.
//
// Assertions see the instance's globals as gvals(s, f), a list of values
// by index. lift asks for globs_ok(s, f): the instance's global addresses
// are in the store and distinct, so global.set changes one entry of the
// list (gvals_set). Global values can be any Value; global.set's rule is
// for numbers (an i32.const, ... before it), as the other rules are.

///|
fn prove_global_rules() -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let wstore = @ind_types.cases("wstore")
  let globs_get = lemma(
    "s_globs_update_get",
    "∀ v : List[Global], ∀ s : Wstore, s_globs(s_globs_update(v, s)) == v",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(s, wstore)),
      @simp.rewrite_tac(ths([@wasm.thm("s_globs_update"), @wasm.thm("s_globs")])),
    ]),
  )
  let mems_globs = lemma(
    "s_mems_globs_update",
    "∀ v : List[Global], ∀ s : Wstore, s_mems(s_globs_update(v, s)) == s_mems(s)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(s, wstore)),
      @simp.rewrite_tac(ths([@wasm.thm("s_globs_update"), @wasm.thm("s_mems")])),
    ]),
  )
  let g_val_get = lemma(
    "g_val_update_get",
    "∀ v : Value, ∀ g : Global, g_val(g_val_update(v, g)) == v",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(tm("(g : Global)"), @ind_types.cases("global"))),
      @simp.rewrite_tac(ths([@wasm.thm("g_val_update"), @wasm.thm("g_val")])),
    ]),
  )
  let el_update = thm("el_list_update")
  let length_update = thm("length_list_update")
  let el_update_other = lemma(
    "el_list_update_other",
    "∀ l : List[A], ∀ i : Num, ∀ k : Num, ∀ x : A, !(k == i) → EL(k, list_update(l, i, x)) == EL(k, l)",
    seq([
      @lists.list_induct_tac,
      @tactics.gen_tac,
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.spec(tm("(i : Num)"), @nums.num_cases())),
      @tactics.struct_cases_tac(@bool.spec(tm("(k : Num)"), @nums.num_cases())),
      @simp.asm_rewrite_tac(
        ths([
          @wasm.thm("list_update"),
          @lists.el(),
          @lists.hd(),
          @lists.tl(),
          arith("∀ m : Num, ∀ n : Num, (SUC(m) == SUC(n)) == (m == n)"),
          arith("∀ n : Num, !(SUC(n) == 0) && !(0 == SUC(n))"),
        ]),
      ),
    ]),
  )
  let globs = "inst_globs(f_inst((f : Wframe)))"
  let el_gvals = lemma(
    "el_gvals",
    "∀ s : Wstore, ∀ f : Wframe, ∀ i : Num, i < LENGTH(gvals(s, f)) → EL(i, gvals(s, f)) == sglob_val(s, f_inst(f), i)",
    seq([
      @simp.rewrite_tac(
        ths([thm("gvals"), @lists.length_map(), @wasm.thm("sglob_val"), @wasm.thm("sglob"), @wasm.thm("sglob_ind")]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_simp_tac(ths([@lists.el_map()])),
    ]),
  )
  let set = "supdate_glob((s : Wstore), f_inst((f : Wframe)), (i : Num), (v : Value))"
  let unfold_set = [
    thm("globs_ok"),
    thm("gvals"),
    @wasm.thm("supdate_glob"),
    @wasm.thm("update_glob"),
    @wasm.thm("sglob_ind"),
    globs_get,
    mems_globs,
    @lists.length_map(),
  ]
  let globs_ok_set = lemma(
    "globs_ok_set",
    "∀ s : Wstore, ∀ f : Wframe, ∀ i : Num, ∀ v : Value, globs_ok(s, f) → globs_ok(\{set}, f)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths(unfold_set + [length_update])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let mems_set = lemma(
    "s_mems_set",
    "∀ s : Wstore, ∀ f : Wframe, ∀ i : Num, ∀ v : Value, s_mems(\{set}) == s_mems(s)",
    @simp.rewrite_tac(ths(unfold_set)),
  )
  let gvals_set = lemma(
    "gvals_set",
    "∀ s : Wstore, ∀ f : Wframe, ∀ i : Num, ∀ v : Value, globs_ok(s, f) && i < LENGTH(gvals(s, f)) → gvals(\{set}, f) == list_update(gvals(s, f), i, v)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths(unfold_set)),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.pure_once_rewrite_tac(ths([@lists.list_eq()])),
      @simp.rewrite_tac(ths([@lists.length_map(), length_update])),
      @tactics.x_gen_tac(tm("(n : Num)")),
      @tactics.disch_tac,
      have(
        "EL((i : Num), \{globs}) < LENGTH(s_globs((s : Wstore)))",
        @meson.asm_meson_tac(ths([])),
      ),
      @tactics.thenl(
        @class.asm_cases_tac(tm("(n : Num) == (i : Num)")),
        @list.List([
          // the global that is set
          seq([
            subst_vars(),
            @simp.asm_simp_tac(ths([@lists.el_map(), el_update, @lists.length_map(), g_val_get])),
          ]),
          // another global: its address differs
          seq([
            have(
              "!(EL((n : Num), \{globs}) == EL((i : Num), \{globs}))",
              @meson.asm_meson_tac(ths([])),
            ),
            @simp.asm_simp_tac(ths([@lists.el_map(), el_update_other, @lists.length_map()])),
          ]),
        ]),
      ),
    ]),
  )
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let v_to_e = @wasm.thm("v_to_e")
  let lfill = @wasm.thm("lfill")
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  // global.get
  let get = "Basic(Global_get((i : Num)))"
  let arity = prove_arities("global_get", get, 0)
  let prefix = @bool.gen_all(prove_prefix("global_get", [], get, arity))
  let cases = @wasm.step_cases(s, f, tm("[\{get}]"), compute=false)
  let gval = "v_to_e(sglob_val((s : Wstore), f_inst((f : Wframe)), (i : Num)))"
  let _ = lemma(
    "sl_global_get",
    "∀ p : \{sassn}, ∀ i : Num, sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => i < LENGTH(gs) && p(vs, ls, gs, h), [Global_get(i)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [EL(i, gs)]) && i < LENGTH(gs) && p(vs0, ls, gs, h)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.rewrite_tac(ths([@lists.map()])),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(s),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs : List[Value])), [\{gval}])")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs : List[Value]), NIL)"), tm("[\{get}]"), s, f, tm("[\{gval}]")]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_accept_tac(rb[10]),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.asm_rewrite_tac(ths(opt)),
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([thm("map_snoc")])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts())),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.exists_tac(tm("(vs : List[Value])")),
            @simp.asm_simp_tac(ths([el_gvals])),
          ]),
        ]),
      ),
    ]),
  )
  // global.set of a number
  let set_step = lemma(
    "global_set_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ i : Num, ∀ c : V_num, reduce_base(s, f, [Basic(EConstNum(c)), Basic(Global_set(i))], supdate_glob(s, f_inst(f), i, V_num(c)), f, NIL)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([@equal.gsym(v_to_e)])),
      @tactics.match_mp_tac(rb[11]),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let c = "Basic(EConstNum((c : V_num)))"
  let setx = "Basic(Global_set((i : Num)))"
  let code = "[\{c}, \{setx}]"
  let arity = prove_arities("global_set", setx, 1)
  let prefix = @bool.gen_all(prove_prefix("global_set", [c], setx, arity))
  let cases = @wasm.step_cases(s, f, tm(code), compute=false)
  let set_c = "supdate_glob((s : Wstore), f_inst((f : Wframe)), (i : Num), V_num((c : V_num)))"
  let _ = lemma(
    "sl_global_set",
    "∀ p : \{sassn}, ∀ i : Num, ∀ c : V_num, sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(c)]) && i < LENGTH(gs) && p(vs0, ls, gs, h)), [Global_set(i)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => (∃ gs0 : List[Value], gs == list_update(gs0, i, V_num(c)) && i < LENGTH(gs0) && p(vs, ls, gs0, h)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      have(
        "gvals(\{set_c}, (f : Wframe)) == list_update(gvals((s : Wstore), f), (i : Num), V_num((c : V_num)))",
        seq([@tactics.match_mp_tac(gvals_set), @simp.asm_rewrite_tac(ths([]))]),
      ),
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), v_to_e, @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(tm(set_c)),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("MAP(v_to_e, (vs0 : List[Value]))")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs0 : List[Value]), NIL)"), tm(code), tm(set_c), f, tm("(NIL : List[Einstr])")]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append(), @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_accept_tac(set_step),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.asm_rewrite_tac(ths(opt)),
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @simp.asm_rewrite_tac(ths(opt)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([@lists.append_nil()])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts() + [mems_set])),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_simp_tac(ths([globs_ok_set])),
            @tactics.exists_tac(tm("gvals((s : Wstore), (f : Wframe))")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}
