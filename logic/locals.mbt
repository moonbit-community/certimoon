// Rules for local.get, local.set and local.tee.
//
// Assertions see the locals as f_locs(f), a list of values by index. The
// reduction rules for local.get and local.set take the locals split at the
// index, vi ++ [v] ++ vs with LENGTH(vi) = k (split_at, in facts.mbt);
// local_get_cases and local_set_cases restate their steps for any frame.
// local.tee steps to [c, c, local.set k], so its rule comes from sl_const
// and sl_local_set.

///|
fn prove_local_rules() -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let split_at = thm("split_at")
  let el_split = thm("el_split")
  let update_split = thm("list_update_split")
  let frame = [@wasm.thm("f_locs"), @wasm.thm("f_inst"), @wasm.thm("f_locs_update")]
  let locs_update = lemma(
    "f_locs_update_get",
    "∀ l : List[Value], ∀ f : Wframe, ∀ s : Wstore, f_locs(f_locs_update(l, f)) == l && f_inst(f_locs_update(l, f)) == f_inst(f) && gvals(s, f_locs_update(l, f)) == gvals(s, f) && (globs_ok(s, f_locs_update(l, f)) == globs_ok(s, f))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(f, @ind_types.cases("wframe"))),
      @simp.rewrite_tac(ths(frame + [thm("gvals"), thm("globs_ok")])),
    ]),
  )
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let v_to_e = @wasm.thm("v_to_e")
  let lfill = @wasm.thm("lfill")
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  // local.get
  let get = "Basic(Local_get((k : Num)))"
  let arity = prove_arities("local_get", get, 0)
  let prefix_get = @bool.gen_all(prove_prefix("local_get", [], get, arity))
  let cases = @wasm.step_cases(s, f, tm("[\{get}]"), compute=false)
  let lval = "v_to_e(EL((k : Num), f_locs((f : Wframe))))"
  let get_step = lemma(
    "local_get_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ k : Num, k < LENGTH(f_locs(f)) → reduce_base(s, f, [Basic(Local_get(k))], s, f, [v_to_e(EL(k, f_locs(f)))])",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(split_at)(th))),
      @tactics.match_mp_tac(@simp.rewrite_rule(ths([@lists.append()]))(rb[8])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let get_cases = lemma(
    "local_get_cases",
    "∀ s : Wstore, ∀ f : Wframe, ∀ k : Num, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, [Basic(Local_get(k))], s2, f2, es2) → s2 == s && f2 == f && es2 == [v_to_e(EL(k, f_locs(f)))]",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.asm_rewrite_tac(ths([@lists.append(), el_split])),
    ]),
  )
  // local.set of a number
  let c = "Basic(EConstNum((c : V_num)))"
  let setx = "Basic(Local_set((k : Num)))"
  let code = "[\{c}, \{setx}]"
  let arity = prove_arities("local_set", setx, 1)
  let prefix_set = @bool.gen_all(prove_prefix("local_set", [c], setx, arity))
  let cases = @wasm.step_cases(s, f, tm(code), compute=false)
  let set_f = "f_locs_update(list_update(f_locs((f : Wframe)), (k : Num), V_num((c : V_num))), f)"
  let set_step = lemma(
    "local_set_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ k : Num, ∀ c : V_num, k < LENGTH(f_locs(f)) → reduce_base(s, f, [Basic(EConstNum(c)), Basic(Local_set(k))], s, f_locs_update(list_update(f_locs(f), k, V_num(c)), f), NIL)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(f, @ind_types.cases("wframe"))),
      @simp.rewrite_tac(ths(frame)),
      @tactics.disch_then(th => @tactics.strip_assume_tac(@drule.match_mp(split_at)(th))),
      @tactics.first_x_assum(th => @tactics.subst1_tac(th)),
      subst_vars(),
      @simp.rewrite_tac(ths([update_split, @equal.gsym(v_to_e)])),
      @tactics.match_mp_tac(@simp.rewrite_rule(ths([@lists.append()]))(rb[9])),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let set_cases = lemma(
    "local_set_cases",
    "∀ s : Wstore, ∀ f : Wframe, ∀ k : Num, ∀ c : V_num, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, [Basic(EConstNum(c)), Basic(Local_set(k))], s2, f2, es2) → s2 == s && es2 == NIL && f2 == f_locs_update(list_update(f_locs(f), k, V_num(c)), f)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths(frame + [@lists.append(), update_split])),
    ]),
  )
  // the rules
  let _ = lemma(
    "sl_local_get",
    "∀ p : \{sassn}, ∀ k : Num, sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => k < LENGTH(ls) && p(vs, ls, gs, ms, h), [Local_get(k)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [EL(k, ls)]) && k < LENGTH(ls) && p(vs0, ls, gs, ms, h)))",
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
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs : List[Value])), [\{lval}])")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs : List[Value]), NIL)"), tm("[\{get}]"), s, f, tm("[\{lval}]")]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(get_step),
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix_get)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(get_cases)(th))),
            subst_vars(),
            @simp.rewrite_tac(ths([thm("map_snoc")])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts())),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.exists_tac(tm("(vs : List[Value])")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  let sl_local_set = lemma(
    "sl_local_set",
    "∀ p : \{sassn}, ∀ k : Num, ∀ c : V_num, sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(c)]) && k < LENGTH(ls) && p(vs0, ls, gs, ms, h)), [Local_set(k)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ ls0 : List[Value], ls == list_update(ls0, k, V_num(c)) && k < LENGTH(ls0) && p(vs, ls0, gs, ms, h)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
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
            @tactics.exists_tac(s),
            @tactics.exists_tac(tm(set_f)),
            @tactics.exists_tac(tm("MAP(v_to_e, (vs0 : List[Value]))")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs0 : List[Value]), NIL)"), tm(code), s, tm(set_f), tm("(NIL : List[Einstr])")]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append(), @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(set_step),
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix_set)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(set_cases)(th))),
            subst_vars(),
            @simp.rewrite_tac(ths([@lists.append_nil()])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts() + [locs_update])),
            @tactics.exists_tac(tm("(j : Num)")),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.exists_tac(tm("f_locs((f : Wframe))")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  // local.tee: [c, local.tee k] steps to [c, c, local.set k]; that is
  // i32.const c then local.set k from the same precondition
  let pre = "(vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num((c : V_num))]) && (k : Num) < LENGTH(ls) && (p : \{sassn})(vs0, ls, gs, ms, h))"
  let post = "(vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ ls0 : List[Value], vs == APPEND(vs0, [V_num((c : V_num))]) && ls == list_update(ls0, (k : Num), V_num(c)) && k < LENGTH(ls0) && (p : \{sassn})(vs0, ls0, gs, ms, h))"
  let below = "(vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num((c : V_num))]) && (p : \{sassn})(vs0, ls, gs, ms, h))"
  let t1 = beta(@bool.ispecl(@list.List([tm(pre), tm("(c : V_num)")]), thm("sl_const")))
  let t2 = beta(@bool.ispecl(@list.List([tm(below), tm("(k : Num)"), tm("(c : V_num)")]), sl_local_set))
  let body = then_rule(t1, t2, reassoc=false)
  let (p1, _, q1) = triple_parts(body)
  let body = @drule.match_mp(thm("sl_conseq"))(
    @bool.conj(entails(p1, p1, reassoc=false), @bool.conj(body, entails(q1, tm(post), reassoc=false))),
  )
  let body = @simp.rewrite_rule(ths([thm("sl_triple"), thm("triple")]))(body)
  let tee = "Basic(Local_tee((k : Num)))"
  let arity = prove_arities("local_tee", tee, 1)
  let prefix_tee = @bool.gen_all(prove_prefix("local_tee", [c], tee, arity))
  let cases = @wasm.step_cases(s, f, tm("[\{c}, \{tee}]"), compute=false)
  let then_set = "[\{c}, \{c}, \{setx}]"
  let rb_lift = rb[0]
  let _ = lemma(
    "sl_local_tee",
    "∀ p : \{sassn}, ∀ k : Num, ∀ c : V_num, sl_triple(\{pre}, [Local_tee(k)], \{post})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      // the stack is vs0 ++ [c]; keep the precondition for the body
      @tactics.first_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
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
            @tactics.exists_tac(s),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), \{then_set})")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs0 : List[Value]), NIL)"), tm("[\{c}, \{tee}]"), s, f, tm(then_set)]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(rb_lift),
            @simp.rewrite_tac(ths([@equal.gsym(v_to_e)])),
            @tactics.match_accept_tac(rs[37]),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix_tee)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.asm_rewrite_tac(ths(opt)),
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            // the rest is the body, from the same precondition
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([
                  tm("(r : \{hprop})"),
                  s,
                  f,
                  tm("APPEND((vs0 : List[Value]), [V_num((c : V_num))])"),
                  tm("(n' : Num)"),
                ]),
                body,
              ),
            ),
            @simp.rewrite_tac(
              ths([@lists.map_append(), @lists.map(), v_to_e, @equal.gsym(@lists.append_assoc()), @lists.append()]),
            ),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @meson.asm_meson_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}
