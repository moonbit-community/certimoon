// The rule for call.
//
// A call of function j steps to Invoke(sfunc_ind(inst, j)) (call_step),
// which takes the function's arguments off the stack and becomes a frame
// around its body, with the arguments and the locals' zeros as its locals
// (invoke_step). The frame is safe while the body is (frame_safe,
// label_safe), so the call is (call_safe); sl_call says that for module
// triples, given a spec of the function's body.

///|
fn prove_call_steps() -> Unit raise {
  let call_x = "Basic(Call((j : Num)))"
  let arity = prove_arities("call", call_x, 0)
  let prefix = prove_prefix("call", [], call_x, arity)
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let cases = @bool.gen_all(@wasm.step_cases(s, f, tm("[\{call_x}]"), compute=false))
  let _ = lemma(
    "call_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ j : Num, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, APPEND(MAP(v_to_e, vs0), [Basic(Call(j))]), s2, f2, es2) → s2 == s && f2 == f && es2 == APPEND(MAP(v_to_e, vs0), [Invoke(sfunc_ind(f_inst(f), j))])",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(cases)(th))),
      subst_vars(),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let rb = @wasm.thm("reduce_base_rules")
  let _ = lemma(
    "call_can_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ j : Num, reduce(s, f, APPEND(MAP(v_to_e, vs0), [Basic(Call(j))]), s, f, APPEND(MAP(v_to_e, vs0), [Invoke(sfunc_ind(f_inst(f), j))]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(thm("reduce_after_vals")),
      @tactics.match_accept_tac(rule_with(rb, ["Call(", "Invoke(sfunc_ind"])),
    ]),
  )
  // the native function a is the one invoked
  let native = "EL(a, s_funcs(s)) == Func_native(i, Tf(t1s, t2s), ts, es) && n_zeros(ts) == SOME(zs)"
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ a : Num, ∀ i : Inst, ∀ t1s : List[Valtype], ∀ t2s : List[Valtype], ∀ ts : List[Valtype], ∀ es : List[B_e], ∀ zs : List[Value]"
  let body = "Frame(LENGTH(t2s), Wframe(APPEND(vcs, zs), i), [Label(LENGTH(t2s), NIL, MAP(Basic, es))])"
  let cl = [
    @ind_types.injectivity("cl"),
    @ind_types.distinctness("cl"),
    @equal.gsym(@ind_types.distinctness("cl")),
    @ind_types.injectivity("tf"),
    @ind_types.option_inj(),
  ]
  let noinvoke = @bool.gen_all(
    prove_arity(
      "noinvoke_simple",
      "reduce_simple",
      "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [Invoke((a : Num))]), e2) && ALL(is_val, suf) → false",
      [thm("no_trap_x"), @ind_types.distinctness("einstr")],
    ),
  )
  let _ = lemma(
    "invoke_base",
    "\{vars}, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], \{native} && reduce_base(s, f, APPEND(suf, [Invoke(a)]), s2, f2, e2) && ALL(is_val, suf) → (∃ vcs : List[Value], suf == MAP(v_to_e, vcs) && LENGTH(vcs) == LENGTH(t1s) && s2 == s && f2 == f && e2 == [\{body}])",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.first_x_assum(th => if @basics.strip_comb(@kernel.concl(th)).0 is Const("reduce_base", _) {
        @tactics.strip_assume_tac(
          @equal.conv_rule(
            @equal.thenc(@simp.pure_once_rewrite_conv(ths([@wasm.thm("reduce_base_cases")])), arity_conv),
            th,
          ),
        )
      } else {
        @tactics.no_tac
      }),
      subst_vars(),
      // no simple step ends with an invoke
      @tactics.try_tac(solve(seq([forward2(noinvoke), @simp.rewrite_tac(ths([]))]))),
      // the invoked function is ours: compare it, and its zeros, with the rule's
      merge_by("EL"),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(cl))),
      split_conjs(),
      subst_vars(),
      // the same types now: the same zeros
      @tactics.try_tac(merge_by("n_zeros")),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(cl))),
      split_conjs(),
      subst_vars(),
      @tactics.try_tac(@tactics.first_assum(th => @tactics.contr_tac(th))),
      @tactics.exists_tac(tm("(vcs : List[Value])")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}

///|
/// An invoke of a native function steps only to its frame, and does.
fn prove_invoke_steps() -> Unit raise {
  let native = "EL(a, s_funcs(s)) == Func_native(i, Tf(t1s, t2s), ts, es) && n_zeros(ts) == SOME(zs) && LENGTH(args) == LENGTH(t1s)"
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ args : List[Value], ∀ a : Num, ∀ i : Inst, ∀ t1s : List[Valtype], ∀ t2s : List[Valtype], ∀ ts : List[Valtype], ∀ es : List[B_e], ∀ zs : List[Value]"
  let code = "APPEND(MAP(v_to_e, APPEND(vs0, args)), [Invoke(a)])"
  let frame = "APPEND(MAP(v_to_e, vs0), [Frame(LENGTH(t2s), Wframe(APPEND(args, zs), i), [Label(LENGTH(t2s), NIL, MAP(Basic, es))])])"
  let einstr_d = @ind_types.distinctness("einstr")
  let _ = lemma(
    "invoke_step",
    "\{vars}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], \{native} && reduce(s, f, \{code}, s2, f2, es2) → s2 == s && f2 == f && es2 == \{frame}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(s : Wstore)"),
            tm("(f : Wframe)"),
            tm("MAP(v_to_e, APPEND((vs0 : List[Value]), (args : List[Value])))"),
            tm("Invoke((a : Num))"),
            tm("(s2 : Wstore)"),
            tm("(f2 : Wframe)"),
            tm("(es2 : List[Einstr])"),
          ]),
          @wasm.thm("step_basic"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([@wasm.thm("all_vals_map"), einstr_d])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      have(
        "ALL(is_val, (suf : List[Einstr]))",
        seq([
          @tactics.mp_tac(@bool.ispec(tm("APPEND((vs0 : List[Value]), (args : List[Value]))"), @wasm.thm("all_vals_map"))),
          @simp.asm_rewrite_tac(ths([@lists.all_append()])),
          @meson.meson_tac(ths([])),
        ]),
      ),
      forward2_3(thm("invoke_base")),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.map_append()]))),
      have(
        "MAP(v_to_e, (vs0 : List[Value])) == (pre : List[Einstr]) && MAP(v_to_e, (args : List[Value])) == MAP(v_to_e, (vcs : List[Value]))",
        seq([@tactics.match_mp_tac(thm("append_len_eq")), @simp.asm_rewrite_tac(ths([@lists.length_map()]))]),
      ),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("map_v_to_e_inj")]))),
      split_conjs(),
      subst_vars(),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let rb = @wasm.thm("reduce_base_rules")
  let _ = lemma(
    "invoke_can_step",
    "\{vars}, \{native} → reduce(s, f, \{code}, s, f, \{frame})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.rewrite_tac(ths([@lists.map_append(), @equal.gsym(@lists.append_assoc())])),
      @tactics.match_mp_tac(thm("reduce_after_vals")),
      @tactics.match_mp_tac(rule_with(rb, ["Func_native"])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}

///|
/// A call is safe when the function's frame is: two steps (to the invoke,
/// then to the frame), then frame_safe.
fn prove_call_safe() -> Unit raise {
  let a = assn
  let safel = thm("safel")
  let unfold = @tactics.conv_tac(@simp.once_rewrite_conv(ths([safel])))
  let n_cases = (v : String) => @tactics.struct_cases_tac(@bool.spec(tm("(\{v} : Num)"), @nums.num_cases()))
  let content = "[Label(LENGTH(t2s), NIL, MAP(Basic, es))]"
  let callee = "Wframe(APPEND(args, zs), i)"
  let native = "EL(sfunc_ind(f_inst(f), j), s_funcs(s)) == Func_native(i, Tf(t1s, t2s), ts, es) && n_zeros(ts) == SOME(zs) && LENGTH(args) == LENGTH(t1s)"
  let _ = lemma(
    "call_safe",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ args : List[Value], ∀ j : Num, ∀ i : Inst, ∀ t1s : List[Valtype], ∀ t2s : List[Valtype], ∀ ts : List[Valtype], ∀ es : List[B_e], ∀ zs : List[Value], ∀ qin : \{a}, ∀ q : \{a}, ∀ l : List[\{a}], \{native} && (∀ k : Num, safel(k, s, \{callee}, \{content}, qin, NIL)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qin(s2, f2, vs) → q(s2, f, APPEND(vs0, vs))) → safel(n, s, f, APPEND(MAP(v_to_e, APPEND(vs0, args)), [Basic(Call(j))]), q, l)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      n_cases("n"),
      unfold,
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(tm("(s : Wstore)")),
            @tactics.exists_tac(tm("(f : Wframe)")),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, APPEND((vs0 : List[Value]), (args : List[Value]))), [Invoke(sfunc_ind(f_inst((f : Wframe)), (j : Num)))])")),
            @tactics.match_accept_tac(thm("call_can_step")),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(thm("call_step"))(th))),
            subst_vars(),
            n_cases("n'"),
            unfold,
            @tactics.disj2_tac,
            @tactics.disj2_tac,
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  @tactics.mp_tac(
                    @bool.mp(
                      @bool.ispecl(
                        @list.List(
                          [
                            "(s : Wstore)", "(f : Wframe)", "(vs0 : List[Value])", "(args : List[Value])",
                            "sfunc_ind(f_inst((f : Wframe)), (j : Num))", "(i : Inst)", "(t1s : List[Valtype])",
                            "(t2s : List[Valtype])", "(ts : List[Valtype])", "(es : List[B_e])", "(zs : List[Value])",
                          ].map(tm),
                        ),
                        thm("invoke_can_step"),
                      ),
                      // the conjunction of three assumptions (one each)
                      @bool.conj(
                        @kernel.assume_rule(tm("EL(sfunc_ind(f_inst((f : Wframe)), (j : Num)), s_funcs((s : Wstore))) == Func_native((i : Inst), Tf((t1s : List[Valtype]), (t2s : List[Valtype])), (ts : List[Valtype]), (es : List[B_e]))")),
                        @bool.conj(
                          @kernel.assume_rule(tm("n_zeros((ts : List[Valtype])) == SOME((zs : List[Value]))")),
                          @kernel.assume_rule(tm("LENGTH((args : List[Value])) == LENGTH((t1s : List[Valtype]))")),
                        ),
                      ),
                    ),
                  ),
                  @tactics.disch_then(th => seq([
                    @tactics.exists_tac(tm("(s : Wstore)")),
                    @tactics.exists_tac(tm("(f : Wframe)")),
                    @tactics.exists_tac(@basics.strip_comb(@kernel.concl(th)).1.to_array()[5]),
                    @tactics.accept_tac(th),
                  ])),
                ]),
                seq([
                  @tactics.repeat_tac(@tactics.strip_tac),
                  forward2_3(thm("invoke_step")),
                        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                  subst_vars(),
                        @tactics.match_mp_tac(thm("frame_safe")),
                  @tactics.exists_tac(tm("(qin : \{a})")),
                  @tactics.conj_tac,
                  @tactics.first_assum(th => @tactics.match_accept_tac(th)),
                ]),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}

///|
/// sl_call: a call of function j of the module, whose body es is proved
/// from the arguments (and the locals' zeros) to results Q, with a br out
/// of it to the same Q.
fn prove_sl_call() -> Unit raise {
  let a = assn
  let sa = sassn
  let fprop = "(List[Value], List[Value], Num, \{heap}) -> Bool"
  let label_top = lemma(
    "label_safe_top",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ m : Num, ∀ li : List[Einstr], ∀ qb : \{a}, safel(n, s, f, li, qb, [qb]) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qb(s2, f2, vs) → LENGTH(vs) == m) → safel(n, s, f, [Label(m, NIL, li)], qb, NIL)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            ["(n : Num)", "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(m : Num)", "(NIL : List[Einstr])", "(li : List[Einstr])", "(qb : \{a})", "(qb : \{a})", "(qb : \{a})", "(NIL : List[\{a}])"].map(tm),
          ),
          thm("label_safe"),
        ),
      ),
      @simp.rewrite_tac(ths([@lists.map(), @lists.append(), @lists.append_nil()])),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first(@list.List([
        solve(@meson.asm_meson_tac(ths([]))),
        solve(seq([@tactics.match_mp_tac(thm("safel_vals")), @tactics.first_assum(th => @tactics.accept_tac(th))])),
      ])),
    ]),
  )
  let pre_b = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == APPEND(args, zs) && P(args, gs, ms, h)"
  let post_b = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => Q(vs, gs, ms, h)"
  let pre_c = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ args : List[Value], vs == APPEND(vs0, args) && LENGTH(args) == LENGTH(t1s) && lc == lc0 && P(args, gs, ms, h)"
  let post_c = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ res : List[Value], vs == APPEND(vs0, res) && lc == lc0 && Q(res, gs, ms, h)"
  let qin = "keep((fs : List[Cl]), (inst : Inst), lift(\{post_b}, (r : \{hprop})))"
  let callee = "Wframe(APPEND((args : List[Value]), (zs : List[Value])), (inst : Inst))"
  let frame_facts = [@wasm.thm("f_inst"), @wasm.thm("f_locs"), thm("gvals"), thm("globs_ok")]
  let _ = lemma(
    "sl_call",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ j : Num, ∀ t1s : List[Valtype], ∀ t2s : List[Valtype], ∀ ts : List[Valtype], ∀ es : List[B_e], ∀ zs : List[Value], ∀ P : \{fprop}, ∀ Q : \{fprop}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], ∀ ls : List[\{sa}], EL(sfunc_ind(inst, j), fs) == Func_native(inst, Tf(t1s, t2s), ts, es) && n_zeros(ts) == SOME(zs) && (∀ args : List[Value], LENGTH(args) == LENGTH(t1s) → sl_triple_m(fs, inst, \{pre_b}, es, \{post_b}, [\{post_b}])) && (∀ res : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, Q(res, gs, ms, h) → LENGTH(res) == LENGTH(t2s)) → sl_triple_m(fs, inst, \{pre_c}, [Call(j)], \{post_c}, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.rewrite_tac(ths([thm("sl_triple_m"), thm("triple_l"), thm("keep")])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      subst_only("vs"),
      @simp.rewrite_tac(ths([@lists.map()])),
      @tactics.match_mp_tac(thm("call_safe")),
      @tactics.exists_tac(tm("(inst : Inst)")),
      @tactics.exists_tac(tm("(t1s : List[Valtype])")),
      @tactics.exists_tac(tm("(t2s : List[Valtype])")),
      @tactics.exists_tac(tm("(ts : List[Valtype])")),
      @tactics.exists_tac(tm("(es : List[B_e])")),
      @tactics.exists_tac(tm("(zs : List[Value])")),
      @tactics.exists_tac(tm(qin)),
      @simp.asm_rewrite_tac(ths([])),
      // the caller's facts with its instance written inst
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("gvals"), thm("globs_ok")]))),
      rw_inst("f"),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          // the frame's content is safe: the body's triple, in the callee's frame
          seq([
            @tactics.gen_tac,
            @tactics.match_mp_tac(label_top),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  @tactics.first_x_assum(body => if @basics.is_forall(@kernel.concl(body)) && show(@kernel.concl(body)).contains("sl_triple_m") {
                    @tactics.first_assum(len => @tactics.mp_tac(@drule.match_mp(body)(len)))
                  } else {
                    @tactics.no_tac
                  }),
                  @simp.rewrite_tac(ths([thm("sl_triple_m"), thm("triple_l"), thm("keep"), @lists.map()])),
                  @tactics.disch_then(th => @tactics.mp_tac(
                    @bool.ispecl(@list.List([tm("(r : \{hprop})"), tm("(s : Wstore)"), tm(callee), tm("(NIL : List[Value])"), tm("(k : Num)")]), th),
                  )),
                  @simp.rewrite_tac(ths(lift_facts() + frame_facts + [@lists.map(), @lists.append()])),
                  @tactics.ants_tac,
                  @meson.asm_meson_tac(ths([])),
                  @tactics.disch_then(th => @tactics.accept_tac(th)),
                ]),
                // the body's results have the function's arity
                seq([
                  @tactics.repeat_tac(@tactics.gen_tac),
                  @simp.rewrite_tac(ths([thm("keep")] + lift_facts())),
                  @tactics.repeat_tac(@tactics.strip_tac),
                  @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(thm("star_some"))(th))),
                  @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                  @meson.asm_meson_tac(ths([])),
                ]),
              ]),
            ),
          ]),
          // the body's results, in the caller's frame, are the call's
          seq([
            @tactics.repeat_tac(@tactics.gen_tac),
            @simp.rewrite_tac(ths([thm("keep"), thm("gvals"), thm("globs_ok")] + lift_facts())),
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            rw_inst("f2"),
            @simp.asm_rewrite_tac(ths([])),
            @meson.asm_meson_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}

///|
/// Rewrites the other assumptions with one whose left side is an
/// application of the constant `name` (and drops it): two equations for
/// the same thing become an equation between their right sides.
fn merge_by(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    if @basics.is_eq(c) && @basics.strip_comb(@equal.lhs(c)).0 is Const(n, _) && n == name {
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th])))
    } else {
      @tactics.no_tac
    }
  })
}

///|
/// Splits the assumptions that are conjunctions.
fn split_conjs() -> @tactics.Tactic {
  @tactics.repeat_tac(
    @tactics.first_x_assum(th => if @basics.is_conj(@kernel.concl(th)) {
      @tactics.strip_assume_tac(th)
    } else {
      @tactics.no_tac
    }),
  )
}

///|
/// mp_tac of `lemma` (∀ xs. A && B && C && D → E) at assumptions that
/// match its premises (the first, then the rest), as forward2 does for two.
fn forward2_3(lemma : @kernel.Thm) -> @tactics.Tactic {
  g => {
    let asms = g.0.to_array()
    let prems = @basics.conjuncts(@basics.dest_imp(@basics.strip_forall(@kernel.concl(lemma)).1).0).to_array()
    let n = prems.length()
    // the assumptions each premise matches on its own
    let matches = (p : @kernel.Term, a : @kernel.Thm) => (try Some(@drule.term_match(@list.List([]), p, @kernel.concl(a))) catch {
      _ => None
    }) is Some(_)
    let cands = prems.map(p => asms.filter(a => matches(p, a.1)).map(a => a.1))
    // try every choice of them for the premises, in order
    fn go(k : Int, chosen : Array[@kernel.Thm]) -> @kernel.Thm? {
      if k == n {
        let mut c = chosen[n - 1]
        for j = n - 2; j >= 0; j = j - 1 {
          c = @bool.conj(chosen[j], c) catch { _ => return None }
        }
        return try Some(@drule.match_mp(lemma)(c)) catch { _ => None }
      }
      for a in cands[k] {
        if go(k + 1, chosen + [a]) is Some(th) {
          return Some(th)
        }
      }
      None
    }
    match go(0, []) {
      Some(th) => @tactics.mp_tac(th)(g)
      None => raise Failure("forward2_3: no assumptions match")
    }
  }
}

///|
/// Substitutes the assumption `x == t` (or `t == x`), x the variable named
/// `name`, everywhere.
fn subst_only(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    let is_it = (t : @kernel.Term) => t is Var(n, _) && n == name
    if @basics.is_eq(c) && (is_it(@equal.lhs(c)) || is_it(@equal.rhs(c))) {
      @tactics.subst_var_tac(th)
    } else {
      @tactics.no_tac
    }
  })
}

///|
/// Rewrites the goal and the other assumptions with the assumption
/// `f_inst(x) == ...`, x the variable named `name`.
fn rw_inst(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    let lhs_ok = @basics.is_eq(c) &&
      @basics.strip_comb(@equal.lhs(c)) is (Const("f_inst", _), args) &&
      args.to_array() is [Var(n, _)] &&
      n == name
    if lhs_ok {
      seq([
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th]))),
        @simp.rewrite_tac(ths([th])),
        @tactics.assume_tac(th),
      ])
    } else {
      @tactics.no_tac
    }
  })
}
