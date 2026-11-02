// What a configuration with a label steps to, and the rule for blocks.
//
// - label_simple, label_base: a base step of [Label(m, e0, li)] leaves
//   the label with li's values, or with [Trap], or takes a br to it;
// - label_steps: a step of APPEND(MAP(v_to_e, vs0), [Label(m, e0, li)]) is
//   a step of li inside the label, or one of those base steps.

///|
fn prove_label_steps() -> Unit raise {
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
  let v_to_e = @wasm.thm("v_to_e")
  let v_to_e_inj = lemma(
    "v_to_e_inj",
    "∀ a : Value, ∀ b : Value, v_to_e(a) == v_to_e(b) == (a == b)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.spec(tm("(a : Value)"), @ind_types.cases("value"))),
      @tactics.struct_cases_tac(@bool.spec(tm("(b : Value)"), @ind_types.cases("value"))),
      @simp.rewrite_tac(ths([v_to_e] + ctor)),
    ]),
  )
  let _ = lemma(
    "map_v_to_e_inj",
    "∀ a : List[Value], ∀ b : List[Value], MAP(v_to_e, a) == MAP(v_to_e, b) == (a == b)",
    seq([
      @lists.list_induct_tac,
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.ispec(tm("(b : List[Value])"), @lists.list_cases())),
      @simp.asm_rewrite_tac(
        ths([@lists.map(), @lists.not_cons_nil(), @equal.gsym(@lists.not_cons_nil()), @lists.cons_11(), v_to_e_inj]),
      ),
    ]),
  )
  let trap_top = @wasm.thm("trap_top")
  let no_trap_label = lemma(
    "no_trap_label",
    "∀ lh : Lholed, ∀ n : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], !Lfilled(0, lh, [Trap], [Label(n, e0, li)])",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      have(
        "trap_top([Label((n : Num), (e0 : List[Einstr]), (li : List[Einstr]))])",
        @meson.asm_meson_tac(ths([@wasm.thm("lfilled_trap_iff")])),
      ),
      @tactics.undisch_tac(tm("trap_top([Label((n : Num), (e0 : List[Einstr]), (li : List[Einstr]))])")),
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
  let label = "Label((m : Num), (e0 : List[Einstr]), (li : List[Einstr]))"
  let result = "((∃ vs : List[Value], li == MAP(v_to_e, vs) && e2 == MAP(v_to_e, vs)) || (li == [Trap] && e2 == [Trap]) || (∃ vs : List[Value], ∃ i : Num, ∃ lh : Lholed, LENGTH(vs) == m && Lfilled(i, lh, APPEND(MAP(v_to_e, vs), [Basic(Br(i))]), li) && e2 == APPEND(MAP(v_to_e, vs), e0)))"
  let simple_cases = @wasm.thm("reduce_simple_cases")
  let finish = seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @meson.asm_meson_tac(ths([no_trap_label])),
  ])
  let label_simple = lemma(
    "label_simple",
    "∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ e2 : List[Einstr], reduce_simple([\{label}], e2) → \{result}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.conv_tac(
        @equal.rator_conv(@equal.rand_conv(@equal.thenc(@simp.pure_once_rewrite_conv(ths([simple_cases])), arity_conv))),
      ),
      finish,
    ]),
  )
  let _ = lemma(
    "label_base",
    "∀ s : Wstore, ∀ f : Wframe, ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, [\{label}], s2, f2, e2) → s2 == s && f2 == f && \{result}",
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
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(label_simple)(th))),
      @meson.meson_tac(ths([])),
    ]),
  )
  let arity = @bool.gen_all(prove_arities("label", label, 0, trap=[thm("no_trap_x"), einstr_d]))
  let lfill = @wasm.thm("lfill")
  let result2 = result.replace_all(old="e2", new="e'")
  let vs0 = "(vs0 : List[Value])"
  let code = "APPEND(MAP(v_to_e, \{vs0}), [\{label}])"
  // the base step is on the label itself
  let in_base = lemma(
    "label_steps_base",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ vsx : List[Value], ∀ rest : List[Einstr], ∀ e : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e' : List[Einstr], \{code} == lfill(LBase(vsx, rest), e) && reduce_base(s, f, e, s2, f2, e') → s2 == s && f2 == f && lfill(LBase(vsx, rest), e') == APPEND(MAP(v_to_e, vs0), e') && \{result2}",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill]))),
      have(
        "last_redex((e : List[Einstr])) || trap_top(e)",
        @meson.asm_meson_tac(ths([@wasm.thm("reduce_base_shape")])),
      ),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([tm("MAP(v_to_e, \{vs0})"), tm(label), tm("(vsx : List[Value])"), tm("(rest : List[Einstr])"), tm("(e : List[Einstr])")]),
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
      @tactics.first_assum(th => @tactics.mp_tac(@drule.match_mp(thm("label_base"))(th))),
      @simp.rewrite_tac(ths([lfill, @lists.append(), @lists.append_nil()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  // the step is inside the label
  let in_label = lemma(
    "label_steps_inside",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ vsx : List[Value], ∀ n : Num, ∀ e1 : List[Einstr], ∀ l : Lholed, ∀ rest : List[Einstr], ∀ e : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e' : List[Einstr], \{code} == lfill(LRec(vsx, n, e1, l, rest), e) && reduce_base(s, f, e, s2, f2, e') → reduce(s, f, li, s2, f2, lfill(l, e')) && lfill(LRec(vsx, n, e1, l, rest), e') == APPEND(MAP(v_to_e, vs0), [Label(m, e0, lfill(l, e'))])",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill]))),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([
            tm("(vsx : List[Value])"),
            tm("MAP(v_to_e, \{vs0})"),
            tm(label),
            tm("Label((n : Num), (e1 : List[Einstr]), lfill((l : Lholed), (e : List[Einstr])))"),
            tm("(rest : List[Einstr])"),
          ]),
          @wasm.thm("snoc_first_nonval"),
        ),
      ),
      @simp.asm_rewrite_tac(
        ths([@wasm.thm("all_vals_map"), @wasm.thm("is_val_clauses"), @ind_types.injectivity("einstr"), thm("map_v_to_e_inj")]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([lfill])),
      @meson.asm_meson_tac(ths([@wasm.thm("decomp_reduce")])),
    ]),
  )
  let _ = lemma(
    "label_steps",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, \{code}, s2, f2, es2) → (∃ li2 : List[Einstr], reduce(s, f, li, s2, f2, li2) && es2 == APPEND(MAP(v_to_e, vs0), [Label(m, e0, li2)])) || (s2 == s && f2 == f && (∃ e2 : List[Einstr], es2 == APPEND(MAP(v_to_e, vs0), e2) && \{result}))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(@wasm.thm("reduce_imp_decomp"))(th))),
      @tactics.disj_cases_tac(@bool.spec(tm("(lh : Lholed)"), @ind_types.cases("lholed"))),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      @tactics.orelse_tac(forward2(in_base), forward2(in_label)),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.asm_rewrite_tac(ths([])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}

///|
/// A br's place in a configuration, and that it does not step.
fn prove_br_facts() -> Unit raise {
  let lfill = @wasm.thm("lfill")
  let depth = @wasm.thm("lh_depth")
  let is_val = [@wasm.thm("is_val_clauses"), @wasm.thm("is_val_basic")]
  let not_cons = [@lists.not_cons_nil(), @equal.gsym(@lists.not_cons_nil())]
  let first_nonval = lemma(
    "first_nonval_eq",
    "∀ a : List[Value], ∀ b : List[Value], ∀ h1 : Einstr, ∀ h2 : Einstr, ∀ t1 : List[Einstr], ∀ t2 : List[Einstr], !is_val(h1) && !is_val(h2) → (APPEND(MAP(v_to_e, a), CONS(h1, t1)) == APPEND(MAP(v_to_e, b), CONS(h2, t2)) == (a == b && h1 == h2 && t1 == t2))",
    seq([
      @lists.list_induct_tac,
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.ispec(tm("(b : List[Value])"), @lists.list_cases())),
      @simp.rewrite_tac(ths([@lists.map(), @lists.append(), @lists.cons_11(), thm("v_to_e_inj")] + not_cons)),
      @tactics.repeat_tac(@tactics.strip_tac),
      // the hypothesis rewrites the rest; h1 or h2 is not a value
      @simp.asm_simp_tac(ths([@theorems.conj_assoc()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.try_tac(@meson.asm_meson_tac(ths(is_val))),
    ]),
  )
  let einstr_d = @ind_types.distinctness("einstr")
  let b_e_d = @ind_types.distinctness("b_e")
  let ctor = [
    einstr_d,
    @equal.gsym(einstr_d),
    @ind_types.injectivity("einstr"),
    b_e_d,
    @equal.gsym(b_e_d),
    @ind_types.injectivity("b_e"),
  ]
  let normal = [
    lfill,
    depth,
    @equal.gsym(@lists.append_assoc()),
    @lists.append(),
    @wasm.thm("map_app_assoc"),
  ]
  let induct = @wasm.thm("lholed_induct")
  let lh2_cases = @tactics.struct_cases_tac(@bool.spec(tm("(lh2 : Lholed)"), @ind_types.cases("lholed")))
  let br_unique = lemma(
    "br_unique",
    "∀ lh1 : Lholed, ∀ lh2 : Lholed, ∀ vs1 : List[Value], ∀ vs2 : List[Value], ∀ k1 : Num, ∀ k2 : Num, lfill(lh1, APPEND(MAP(v_to_e, vs1), [Basic(Br(k1))])) == lfill(lh2, APPEND(MAP(v_to_e, vs2), [Basic(Br(k2))])) → lh_depth(lh1) == lh_depth(lh2) && k1 == k2 && (LENGTH(vs1) == LENGTH(vs2) → vs1 == vs2)",
    @tactics.thenl(
      @tactics.then_tac(@tactics.match_mp_tac(induct), @tactics.conj_tac),
      @list.List([
        seq([@tactics.repeat_tac(@tactics.gen_tac), seq([
          lh2_cases,
          @simp.simp_tac(ths(normal + [first_nonval] + is_val + ctor)),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
          @tactics.try_tac(@meson.asm_meson_tac(ths([thm("append_len_eq"), @arith.add_clauses()]))),
        ])]),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_tac,
          @tactics.repeat_tac(@tactics.gen_tac),
          seq([
          lh2_cases,
          @simp.simp_tac(ths(normal + [first_nonval] + is_val + ctor)),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
          @tactics.try_tac(@meson.asm_meson_tac(ths([thm("append_len_eq"), @arith.add_clauses()]))),
        ]),
        ]),
      ]),
    ),
  )
  let lfilled_one = lemma(
    "lfilled_label",
    "∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ x : List[Einstr], Lfilled(1, LRec(vs0, m, e0, LBase(NIL, NIL), NIL), x, APPEND(MAP(v_to_e, vs0), [Label(m, e0, x)]))",
    seq([
      @simp.rewrite_tac(ths([@wasm.thm("lfilled_eq"), lfill, depth, @lists.map(), @lists.append(), @lists.append_nil()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let reduce_rules = @bool.conjuncts_rule(@wasm.thm("reduce_rules")).to_array()
  let _ = lemma(
    "reduce_label",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ li2 : List[Einstr], reduce(s, f, li, s2, f2, li2) → reduce(s, f, APPEND(MAP(v_to_e, vs0), [Label(m, e0, li)]), s2, f2, APPEND(MAP(v_to_e, vs0), [Label(m, e0, li2)]))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(reduce_rules[38]),
      @meson.asm_meson_tac(ths([lfilled_one])),
    ]),
  )
  let no_trap_top = lemma(
    "no_trap_top_snoc",
    "∀ cs : List[Einstr], ∀ x : Einstr, ALL(is_val, cs) && !(x == Trap) → !trap_top(APPEND(cs, [x]))",
    @meson.meson_tac(ths([thm("no_trap_x"), @equal.gsym(@wasm.thm("lfilled_trap_iff"))])),
  )
  let vals = [@lists.all_append(), @lists.all(), @wasm.thm("all_vals_map")] + is_val + ctor
  let br = "APPEND(MAP(v_to_e, (vs : List[Value])), [Basic(Br((k : Num)))])"
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
  let no_step2 = lemma(
    "br_no_step2",
    "∀ s : Wstore, ∀ f : Wframe, ∀ a : List[Value], ∀ vs : List[Value], ∀ k : Num, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], !reduce(s, f, APPEND(MAP(v_to_e, a), APPEND(MAP(v_to_e, vs), [Basic(Br(k))])), s2, f2, es2)",
    seq([
      @simp.rewrite_tac(ths([@lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(thm("br_no_step")),
      @simp.rewrite_tac(ths([@lists.all_append(), @wasm.thm("all_vals_map")])),
    ]),
  )
  let no_trap_br = lemma(
    "no_trap_top_br",
    "∀ a : List[Value], ∀ vs : List[Value], ∀ k : Num, !trap_top(APPEND(MAP(v_to_e, a), APPEND(MAP(v_to_e, vs), [Basic(Br(k))])))",
    seq([
      @simp.rewrite_tac(ths([@lists.append_assoc()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(no_trap_top),
      @simp.rewrite_tac(ths(vals)),
    ]),
  )
  let no_trap_label_top = lemma(
    "no_trap_top_label",
    "∀ a : List[Value], ∀ n : Num, ∀ e : List[Einstr], ∀ l : List[Einstr], !trap_top(APPEND(MAP(v_to_e, a), [Label(n, e, l)]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(no_trap_top),
      @simp.rewrite_tac(ths(vals)),
    ]),
  )
  let arith1 = arith("∀ a : Num, ∀ b : Num, a + 1 <= b → a <= b")
  let arith2 = arith("∀ a : Num, ∀ b : Num, a + 1 <= b → !(b == a)")
  let _ = lemma(
    "br_stuck",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ k : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], lh_depth(lh) <= k → !reduce(s, f, lfill(lh, \{br}), s2, f2, es2)",
    @tactics.thenl(
      @tactics.then_tac(@tactics.match_mp_tac(induct), @tactics.conj_tac),
      @list.List([
        seq([
          @tactics.x_gen_tac(tm("(a0 : List[Value])")),
          @tactics.x_gen_tac(tm("(a1 : List[Einstr])")),
          @tactics.repeat_tac(@tactics.strip_tac),
          append_step("APPEND(APPEND(MAP(v_to_e, (a0 : List[Value])), MAP(v_to_e, (vs : List[Value]))), [Basic(Br((k : Num)))])", "(a1 : List[Einstr])"),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([no_step2, no_trap_br]))),
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
            "APPEND(MAP(v_to_e, (a0 : List[Value])), [Label((a1 : Num), (a2 : List[Einstr]), lfill((a3 : Lholed), \{br}))])",
            "(a4 : List[Einstr])",
          ),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([no_trap_label_top]))),
          // the trap at the top is gone (its assumption is now false)
          @tactics.try_tac(solve(@simp.asm_rewrite_tac(ths([])))),
          // the four cases of label_steps, in order
          @tactics.thenl(
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(thm("label_steps"))(th))),
            @list.List([
              @meson.asm_meson_tac(ths([arith1])),
              @meson.asm_meson_tac(ths([thm("br_not_vals"), @wasm.thm("all_vals_map")])),
              @meson.asm_meson_tac(ths([thm("br_not_trap")])),
              seq([
                @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@wasm.thm("lfilled_eq")]))),
                @meson.asm_meson_tac(ths([br_unique, arith2])),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "safel_vals",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : \{assn}, ∀ l : List[\{assn}], q(s, f, vs) → safel(n, s, f, MAP(v_to_e, vs), q, l)",
    seq([
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safel")])),
      @meson.meson_tac(ths([])),
    ]),
  )
}
