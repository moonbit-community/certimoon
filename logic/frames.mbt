// What a configuration with a frame steps to (as block.mbt does for
// labels).
//
// - frame_simple, frame_base: a base step of [Frame(m, f1, es)] leaves the
//   frame with es's values, with [Trap], or with the values of a return;
//   or it is a step of es inside, in the frame's own frame f1;
// - frame_steps: a step of APPEND(MAP(v_to_e, vs0), [Frame(m, f1, es)]) is
//   one of those, with vs0 left alone (the frame cannot be the hole of a
//   label context: that holds a label).

///|
fn prove_frame_steps() -> Unit raise {
  let einstr_d = @ind_types.distinctness("einstr")
  let ctor = [
    einstr_d,
    @equal.gsym(einstr_d),
    @ind_types.injectivity("einstr"),
    @ind_types.distinctness("value"),
    @equal.gsym(@ind_types.distinctness("value")),
    @ind_types.injectivity("value"),
    @ind_types.distinctness("b_e"),
    @equal.gsym(@ind_types.distinctness("b_e")),
    @ind_types.injectivity("b_e"),
  ]
  let trap_top = @wasm.thm("trap_top")
  let no_trap_frame = lemma(
    "no_trap_frame",
    "∀ lh : Lholed, ∀ n : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], !Lfilled(0, lh, [Trap], [Frame(n, f1, es)])",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      have(
        "trap_top([Frame((n : Num), (f1 : Wframe), (es : List[Einstr]))])",
        @meson.asm_meson_tac(ths([@wasm.thm("lfilled_trap_iff")])),
      ),
      @tactics.undisch_tac(tm("trap_top([Frame((n : Num), (f1 : Wframe), (es : List[Einstr]))])")),
      @simp.rewrite_tac(
        ths(
          [
            trap_top,
            @wasm.thm("cons_eq_append"),
            @lists.cons_11(),
            @wasm.thm("map_v_to_e_eq_cons"),
            @wasm.thm("eq_v_to_e"),
            @lists.map_eq_nil(),
          ] +
          ctor,
        ),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([@wasm.thm("map_v_to_e_eq_cons"), @wasm.thm("eq_v_to_e"), @lists.cons_11()] + ctor)),
      ),
      @meson.asm_meson_tac(ths(ctor)),
    ]),
  )
  let frame = "Frame((m : Num), (f1 : Wframe), (es : List[Einstr]))"
  let result = "((∃ vs : List[Value], es == MAP(v_to_e, vs) && e2 == MAP(v_to_e, vs)) || (es == [Trap] && e2 == [Trap]) || (∃ vs : List[Value], ∃ i : Num, ∃ lh : Lholed, LENGTH(vs) == m && Lfilled(i, lh, APPEND(MAP(v_to_e, vs), [Basic(Return)]), es) && e2 == MAP(v_to_e, vs)))"
  let frame_simple = lemma(
    "frame_simple",
    "∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ e2 : List[Einstr], reduce_simple([\{frame}], e2) → \{result}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.conv_tac(
        @equal.rator_conv(
          @equal.rand_conv(@equal.thenc(@simp.pure_once_rewrite_conv(ths([@wasm.thm("reduce_simple_cases")])), arity_conv)),
        ),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @meson.asm_meson_tac(ths([no_trap_frame])),
    ]),
  )
  let inner = "(∃ f1' : Wframe, ∃ es' : List[Einstr], reduce(s, f1, es, s2, f1', es') && f2 == f0 && e2 == [Frame(m, f1', es')])"
  let _ = lemma(
    "frame_base",
    "∀ s : Wstore, ∀ f0 : Wframe, ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f0, [\{frame}], s2, f2, e2) → (s2 == s && f2 == f0 && \{result}) || \{inner}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.conv_tac(
        @equal.rator_conv(
          @equal.rand_conv(@equal.thenc(@simp.pure_once_rewrite_conv(ths([@wasm.thm("reduce_base_cases")])), arity_conv)),
        ),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([])),
      @tactics.try_tac(@tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(frame_simple)(th)))),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let arity = @bool.gen_all(prove_arities("frame", frame, 0, trap=[thm("no_trap_x"), einstr_d]))
  let lfill = @wasm.thm("lfill")
  let vs0 = "(vs0 : List[Value])"
  let code = "APPEND(MAP(v_to_e, \{vs0}), [\{frame}])"
  let result2 = result.replace_all(old="e2", new="e'")
  let inner2 = "(∃ f1' : Wframe, ∃ es' : List[Einstr], reduce(s, f1, es, s2, f1', es') && f2 == f0 && e' == [Frame(m, f1', es')])"
  // the base step is on the frame itself
  let in_base = lemma(
    "frame_steps_base",
    "∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ vsx : List[Value], ∀ rest : List[Einstr], ∀ e : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e' : List[Einstr], \{code} == lfill(LBase(vsx, rest), e) && reduce_base(s, f0, e, s2, f2, e') → lfill(LBase(vsx, rest), e') == APPEND(MAP(v_to_e, vs0), e') && ((s2 == s && f2 == f0 && \{result2}) || \{inner2})",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill]))),
      have(
        "last_redex((e : List[Einstr])) || trap_top(e)",
        @meson.asm_meson_tac(ths([@wasm.thm("reduce_base_shape")])),
      ),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([tm("MAP(v_to_e, \{vs0})"), tm(frame), tm("(vsx : List[Value])"), tm("(rest : List[Einstr])"), tm("(e : List[Einstr])")]),
          @wasm.thm("step_basic_lbase"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([@wasm.thm("all_vals_map"), einstr_d])),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "ALL(is_val, (suf : List[Einstr]))",
        seq([
          @tactics.mp_tac(@bool.ispec(tm(vs0), @wasm.thm("all_vals_map"))),
          @simp.asm_rewrite_tac(ths([@lists.all_append()])),
          @meson.meson_tac(ths([])),
        ]),
      ),
      have("LENGTH((suf : List[Einstr])) == 0", seq([@tactics.match_mp_tac(arity), @meson.asm_meson_tac(ths([]))])),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.length_eq_nil()]))),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.append(), @lists.append_nil(), thm("map_v_to_e_inj")]))),
      subst_vars(),
      @tactics.first_assum(th => @tactics.mp_tac(@drule.match_mp(thm("frame_base"))(th))),
      @simp.rewrite_tac(ths([lfill, @lists.append(), @lists.append_nil()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  // a label context's hole holds a label, not this frame
  let not_label = lemma(
    "frame_not_label",
    "∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ vsx : List[Value], ∀ n : Num, ∀ e1 : List[Einstr], ∀ l : Lholed, ∀ rest : List[Einstr], ∀ e : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e' : List[Einstr], \{code} == lfill(LRec(vsx, n, e1, l, rest), e) && reduce_base(s, f0, e, s2, f2, e') → false",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill]))),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(vsx : List[Value])"),
            tm("MAP(v_to_e, \{vs0})"),
            tm(frame),
            tm("Label((n : Num), (e1 : List[Einstr]), lfill((l : Lholed), (e : List[Einstr])))"),
            tm("(rest : List[Einstr])"),
          ]),
          @wasm.thm("snoc_first_nonval"),
        ),
      ),
      @simp.asm_rewrite_tac(
        ths([@wasm.thm("all_vals_map"), @wasm.thm("is_val_clauses")] + ctor),
      ),
    ]),
  )
  let _ = lemma(
    "frame_steps",
    "∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f0, \{code}, s2, f2, es2) → (∃ f1' : Wframe, ∃ es' : List[Einstr], reduce(s, f1, es, s2, f1', es') && f2 == f0 && es2 == APPEND(MAP(v_to_e, vs0), [Frame(m, f1', es')])) || (s2 == s && f2 == f0 && (∃ e2 : List[Einstr], es2 == APPEND(MAP(v_to_e, vs0), e2) && \{result}))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(@wasm.thm("reduce_imp_decomp"))(th))),
      @tactics.disj_cases_tac(@bool.spec(tm("(lh : Lholed)"), @ind_types.cases("lholed"))),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      @tactics.orelse_tac(forward2(in_base), forward2(not_label)),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.asm_rewrite_tac(ths([])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}

///|
/// A return waiting in contexts does not step: only the frame around it
/// takes it.
fn prove_return_stuck() -> Unit raise {
  let einstr = @ind_types.distinctness("einstr")
  let b_e = @ind_types.distinctness("b_e")
  let ctor = [
    einstr,
    @equal.gsym(einstr),
    @ind_types.injectivity("einstr"),
    b_e,
    @equal.gsym(b_e),
    @ind_types.injectivity("b_e"),
  ]
  let lfill = @wasm.thm("lfill")
  let depth = @wasm.thm("lh_depth")
  let not_cons = [@lists.not_cons_nil(), @equal.gsym(@lists.not_cons_nil())]
  let is_val = [@wasm.thm("is_val_clauses"), @wasm.thm("is_val_basic")]
  let ret = "APPEND(MAP(v_to_e, (vs : List[Value])), [Basic(Return)])"
  let ret_code = "lfill((lh : Lholed), \{ret})"
  let _ = lemma(
    "ret_not_vals",
    "∀ lh : Lholed, ∀ vs : List[Value], !ALL(is_val, \{ret_code})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("lfill_vals"))(th))),
      @simp.rewrite_tac(ths([@lists.all_append(), @lists.all()] + is_val + [b_e])),
    ]),
  )
  let _ = lemma(
    "ret_not_trap",
    "∀ lh : Lholed, ∀ vs : List[Value], !(\{ret_code} == [Trap])",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("lfill_trap"))(th))),
      @simp.rewrite_tac(ths([thm("snoc_eq"), @lists.append_eq_nil(), @lists.last(), einstr, @equal.gsym(einstr)] + not_cons)),
    ]),
  )
  let noret_simple = @bool.gen_all(
    prove_arity(
      "noret_simple",
      "reduce_simple",
      "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [Basic(Return)]), e2) && ALL(is_val, suf) → false",
      [thm("no_trap")],
    ),
  )
  let noret = @bool.gen_all(
    prove_arity(
      "noret_base",
      "reduce_base",
      "∀ s : Wstore, ∀ f : Wframe, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, APPEND(suf, [Basic(Return)]), s2, f2, e2) && ALL(is_val, suf) → false",
      [noret_simple],
    ),
  )
  let ret_no_step = lemma(
    "ret_no_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ cs : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], ALL(is_val, cs) → !reduce(s, f, APPEND(cs, [Basic(Return)]), s2, f2, es2)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(s : Wstore)"),
            tm("(f : Wframe)"),
            tm("(cs : List[Einstr])"),
            tm("Basic(Return)"),
            tm("(s2 : Wstore)"),
            tm("(f2 : Wframe)"),
            tm("(es2 : List[Einstr])"),
          ]),
          @wasm.thm("step_basic"),
        ),
      ),
      @simp.asm_rewrite_tac(ths([einstr])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.all_append()]))),
      @meson.asm_meson_tac(ths([noret])),
    ]),
  )
  let no_step2 = lemma(
    "ret_no_step2",
    "∀ s : Wstore, ∀ f : Wframe, ∀ a : List[Value], ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], !reduce(s, f, APPEND(MAP(v_to_e, a), \{ret}), s2, f2, es2)",
    seq([
      @simp.rewrite_tac(ths([@lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(ret_no_step),
      @simp.rewrite_tac(ths([@lists.all_append(), @wasm.thm("all_vals_map")])),
    ]),
  )
  let vals = [@lists.all_append(), @lists.all(), @wasm.thm("all_vals_map")] + is_val + ctor
  let no_trap_ret = lemma(
    "no_trap_top_ret",
    "∀ a : List[Value], ∀ vs : List[Value], !trap_top(APPEND(MAP(v_to_e, a), \{ret}))",
    seq([
      @simp.rewrite_tac(ths([@lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(thm("no_trap_top_snoc")),
      @simp.rewrite_tac(ths(vals)),
    ]),
  )
  let normal = [lfill, depth, @equal.gsym(@lists.append_assoc()), @lists.append(), @wasm.thm("map_app_assoc")]
  let induct = @wasm.thm("lholed_induct")
  let lh2_cases = @tactics.struct_cases_tac(@bool.spec(tm("(lh2 : Lholed)"), @ind_types.cases("lholed")))
  let case_tac = seq([
    lh2_cases,
    @simp.simp_tac(ths(normal + [thm("first_nonval_eq")] + is_val + ctor)),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let br_ret = lemma(
    "br_ret_distinct",
    "∀ lh1 : Lholed, ∀ lh2 : Lholed, ∀ vs1 : List[Value], ∀ vs2 : List[Value], ∀ k : Num, !(lfill(lh1, APPEND(MAP(v_to_e, vs1), [Basic(Br(k))])) == lfill(lh2, APPEND(MAP(v_to_e, vs2), [Basic(Return)])))",
    @tactics.thenl(
      @tactics.then_tac(@tactics.match_mp_tac(induct), @tactics.conj_tac),
      @list.List([
        seq([@tactics.repeat_tac(@tactics.gen_tac), case_tac]),
        seq([@tactics.repeat_tac(@tactics.gen_tac), @tactics.disch_tac, @tactics.repeat_tac(@tactics.gen_tac), case_tac]),
      ]),
    ),
  )
  let assoc = [@equal.gsym(@lists.append_assoc()), @lists.append()]
  let append_step = (es1 : String, es2 : String) => seq([
    @tactics.mp_tac(
      @bool.ispecl(
        @list.List([
          tm("(s : Wstore)"),
          tm("(f : Wframe)"),
          tm(es1),
          tm(es2),
          tm("(s2 : Wstore)"),
          tm("(f2 : Wframe)"),
          tm("(es2 : List[Einstr])"),
        ]),
        @wasm.thm("reduce_append"),
      ),
    ),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill, depth] + assoc))),
    @simp.asm_rewrite_tac(ths(assoc + vals)),
    @tactics.repeat_tac(@tactics.strip_tac),
  ])
  let _ = lemma(
    "return_stuck",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ s : Wstore, ∀ f : Wframe, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], !reduce(s, f, lfill(lh, \{ret}), s2, f2, es2)",
    @tactics.thenl(
      @tactics.then_tac(@tactics.match_mp_tac(induct), @tactics.conj_tac),
      @list.List([
        seq([
          @tactics.x_gen_tac(tm("(a0 : List[Value])")),
          @tactics.x_gen_tac(tm("(a1 : List[Einstr])")),
          @tactics.repeat_tac(@tactics.strip_tac),
          append_step("APPEND(APPEND(MAP(v_to_e, (a0 : List[Value])), MAP(v_to_e, (vs : List[Value]))), [Basic(Return)])", "(a1 : List[Einstr])"),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([no_step2, no_trap_ret]))),
          @meson.asm_meson_tac(ths([])),
        ]),
        seq([
          @tactics.x_gen_tac(tm("(a0 : List[Value])")),
          @tactics.x_gen_tac(tm("(a1 : Num)")),
          @tactics.x_gen_tac(tm("(a2 : List[Einstr])")),
          @tactics.x_gen_tac(tm("(a3 : Lholed)")),
          @tactics.x_gen_tac(tm("(a4 : List[Einstr])")),
          @tactics.disch_tac,
          @tactics.repeat_tac(@tactics.strip_tac),
          append_step(
            "APPEND(MAP(v_to_e, (a0 : List[Value])), [Label((a1 : Num), (a2 : List[Einstr]), lfill((a3 : Lholed), \{ret}))])",
            "(a4 : List[Einstr])",
          ),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("no_trap_top_label")]))),
          @tactics.try_tac(solve(@simp.asm_rewrite_tac(ths([])))),
          // the four cases of label_steps, in order
          @tactics.thenl(
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(thm("label_steps"))(th))),
            @list.List([
              @meson.asm_meson_tac(ths([])),
              @meson.asm_meson_tac(ths([thm("ret_not_vals"), @wasm.thm("all_vals_map")])),
              @meson.asm_meson_tac(ths([thm("ret_not_trap")])),
              seq([
                @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@wasm.thm("lfilled_eq")]))),
                @meson.asm_meson_tac(ths([br_ret])),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
}

///|
/// Safety carries through a frame: the frame steps while its content is
/// safe, and leaves with the content's values.
fn prove_frame_safe() -> Unit raise {
  let a = assn
  let safel = thm("safel")
  let lfill = @wasm.thm("lfill")
  let rs = @wasm.thm("reduce_simple_rules")
  let rb = @wasm.thm("reduce_base_rules")
  // [Frame(n, f, vs)] -> vs, and a step inside the frame
  let frame_vals = {
    let mut found = None
    for r in @bool.conjuncts_rule(rs) {
      let c = @basics.strip_forall(@kernel.concl(r)).1
      let text = show(c)
      if !@basics.is_imp(c) && text.contains("Frame(") && !text.contains("Trap") {
        found = Some(r)
      }
    }
    guard found is Some(r) else { raise Failure("wasmcert/logic: no frame rule") }
    r
  }
  let rb_lift = @bool.conjuncts_rule(rb).to_array()[0]
  let rb_frame = rule_with(rb, ["Frame(", "reduce("])
  let after_vals = lemma(
    "reduce_after_vals",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ e : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, e, s2, f2, e2) → reduce(s, f, APPEND(MAP(v_to_e, vs0), e), s2, f2, APPEND(MAP(v_to_e, vs0), e2))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@bool.ispec(tm("LBase((vs0 : List[Value]), NIL)"), @drule.match_mp(@wasm.thm("decomp_reduce"))(th)))),
      @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
    ]),
  )
  let frame = "Frame((m : Num), (f1 : Wframe), (es : List[Einstr]))"
  let code = "APPEND(MAP(v_to_e, (vs0 : List[Value])), [\{frame}])"
  let no_br = [safel, @lists.length(), arith("∀ i : Num, !(i < 0)")]
  let vals_not_trap = lemma(
    "vals_not_trap",
    "∀ vs : List[Value], !(MAP(v_to_e, vs) == [Trap])",
    seq([
      @tactics.gen_tac,
      @tactics.disch_tac,
      @tactics.mp_tac(@bool.spec(tm("(vs : List[Value])"), @wasm.thm("all_vals_map"))),
      @simp.asm_rewrite_tac(ths([@lists.all(), @wasm.thm("is_val_clauses")])),
    ]),
  )
  let ret_not_map = lemma(
    "ret_not_map",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ vs2 : List[Value], !(lfill(lh, APPEND(MAP(v_to_e, vs), [Basic(Return)])) == MAP(v_to_e, vs2))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.mp_tac(@bool.ispecl(@list.List([tm("(lh : Lholed)"), tm("(vs : List[Value])")]), thm("ret_not_vals"))),
      @simp.asm_rewrite_tac(ths([@wasm.thm("all_vals_map")])),
    ]),
  )
  let impossible = [
    @wasm.thm("reduce_not_vals"),
    @wasm.thm("reduce_not_trap"),
    thm("return_stuck"),
    vals_not_trap,
    @equal.gsym(vals_not_trap),
    ret_not_map,
    @equal.gsym(ret_not_map),
  ]
  let can_step = lemma(
    "frame_can_step",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, safel(SUC(n), s, f1, es, qin, NIL) → (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f0, \{code}, s2, f2, es2))",
    seq([
      @simp.rewrite_tac(ths(no_br)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.first(@list.List([
        // the content is values: the frame leaves with them
        solve(seq([
          @tactics.exists_tac(tm("(s : Wstore)")),
          @tactics.exists_tac(tm("(f0 : Wframe)")),
          @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), MAP(v_to_e, (vs : List[Value])))")),
          @tactics.match_mp_tac(after_vals),
          @tactics.match_mp_tac(rb_lift),
          @tactics.match_accept_tac(frame_vals),
        ])),
        // the content steps: so does the frame
        solve(seq([
          @tactics.exists_tac(tm("(s2 : Wstore)")),
          @tactics.exists_tac(tm("(f0 : Wframe)")),
          @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), [Frame((m : Num), (f2 : Wframe), (es2 : List[Einstr]))])")),
          @tactics.match_mp_tac(after_vals),
          @tactics.match_mp_tac(rb_frame),
          @tactics.first_assum(th => @tactics.accept_tac(th)),
        ])),
      ])),
    ]),
  )
  let next = lemma(
    "frame_next",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], safel(SUC(n), s, f1, es, qin, NIL) && reduce(s, f0, \{code}, s2, f2, es2) → (∃ f1' : Wframe, ∃ es' : List[Einstr], safel(n, s2, f1', es', qin, NIL) && f2 == f0 && es2 == APPEND(MAP(v_to_e, vs0), [Frame(m, f1', es')])) || (s2 == s && f2 == f0 && (∃ vs : List[Value], es2 == MAP(v_to_e, APPEND(vs0, vs)) && qin(s, f1, vs)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(
        @tactics.conjuncts_then2(
          c => @tactics.strip_assume_tac(@simp.rewrite_rule(ths(no_br))(c)),
          c => @tactics.strip_assume_tac(@drule.match_mp(thm("frame_steps"))(c)),
        ),
      ),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@wasm.thm("lfilled_eq"), thm("map_v_to_e_inj")]))),
      // split the conjunctions that rewriting made
      @tactics.repeat_tac(
        @tactics.first_x_assum(th => if @basics.is_conj(@kernel.concl(th)) {
          @tactics.strip_assume_tac(th)
        } else {
          @tactics.no_tac
        }),
      ),
      subst_vars(),
      // the impossible cases: the content is values, a trap or a return,
      // and steps; or it is values and also a trap or a return
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(impossible))),
      @tactics.try_tac(@tactics.first_assum(th => @tactics.contr_tac(th))),
      @tactics.first(@list.List([
        // a step inside
        solve(seq([
          @tactics.disj1_tac,
          @tactics.exists_tac(tm("(f1' : Wframe)")),
          @tactics.exists_tac(tm("(es' : List[Einstr])")),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
          @tactics.first_assum(th => @tactics.accept_tac(th)),
        ])),
        // out, with the values
        solve(seq([
          @tactics.disj2_tac,
          @simp.asm_rewrite_tac(ths([@lists.map_append()])),
          @tactics.exists_tac(tm("(vs : List[Value])")),
          @simp.asm_rewrite_tac(ths([])),
        ])),
      ])),
    ]),
  )
  let _ = lemma(
    "frame_safe",
    "∀ n : Num, ∀ s : Wstore, ∀ f0 : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ f1 : Wframe, ∀ es : List[Einstr], ∀ qin : \{a}, ∀ q : \{a}, ∀ l : List[\{a}], safel(n, s, f1, es, qin, NIL) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs2 : List[Value], qin(s2, f2, vs2) → q(s2, f0, APPEND(vs0, vs2))) → safel(n, s, f0, \{code}, q, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.conv_tac(@simp.once_rewrite_conv(ths([safel]))),
          @tactics.disj2_tac,
          @tactics.disj2_tac,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @meson.asm_meson_tac(ths([can_step])),
              seq([
                @tactics.repeat_tac(@tactics.strip_tac),
                @tactics.first_x_assum(r => @tactics.first_assum(sf => @tactics.mp_tac(@drule.match_mp(next)(@bool.conj(sf, r))))),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_vars(),
                @tactics.first(@list.List([
                  // still inside the frame
                  solve(seq([@tactics.first_x_assum(th => @tactics.match_mp_tac(th)), @meson.asm_meson_tac(ths([]))])),
                  // out of it, with values
                  solve(seq([@tactics.match_mp_tac(thm("safel_vals")), @meson.asm_meson_tac(ths([]))])),
                ])),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
}
