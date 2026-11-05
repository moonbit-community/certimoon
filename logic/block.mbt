// What a configuration with a label steps to, and the rule for blocks.
//
// - label_simple, label_base: a base step of [Label(m, e0, li)] leaves
//   the label with li's values, or with [Trap], or takes a br to it;
// - label_steps: a step of APPEND(MAP(v_to_e, vs0), [Label(m, e0, li)]) is
//   a step of li inside the label, or one of those base steps;
// - br_unique, br_stuck: where a br is in a configuration, and that a br
//   to a label outside the configuration does not step;
// - label_safe: safety carries through a label (blocks and loops use it);
// - sl_block: the rule for blocks with no parameters.

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

///|
/// label_safe: safety carries through a label. The body li is safe with
/// postcondition qb and label 0 assertion lb (then the labels l around);
/// its values vs leave the label as vs0 ++ vs, and a br to it with vs
/// (of the label's arity) continues as vs0 ++ vs ++ e0, safe for as many
/// steps as are left (a loop's continuation is the loop again).
fn prove_label_safe() -> Unit raise {
  let safel = thm("safel")
  let lfill = @wasm.thm("lfill")
  let depth = @wasm.thm("lh_depth")
  let lfilled_eq = @wasm.thm("lfilled_eq")
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let rb_lift = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let einstr_d = @ind_types.distinctness("einstr")
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let vs0 = "(vs0 : List[Value])"
  let label = "Label((m : Num), (e0 : List[Einstr]), (li : List[Einstr]))"
  // a step of vs0 ++ [label] from the base step `inner` -> `out`
  let base_step = (inner : String, out : String, rule : @tactics.Tactic) => seq([
    @tactics.exists_tac(s),
    @tactics.exists_tac(f),
    @tactics.exists_tac(tm("APPEND(MAP(v_to_e, \{vs0}), \{out})")),
    @tactics.mp_tac(
      @bool.ispecl(
        @list.List([s, f, tm("LBase(\{vs0}, NIL)"), tm(inner), s, f, tm(out)]),
        @wasm.thm("decomp_reduce"),
      ),
    ),
    @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
    @tactics.disch_then(th => @tactics.match_mp_tac(th)),
    @tactics.match_mp_tac(rb_lift),
    rule,
  ])
  let steps = (cases : Array[@tactics.Tactic]) => seq([
    @tactics.x_gen_tac(tm("(t1 : Wstore)")),
    @tactics.x_gen_tac(tm("(t2 : Wframe)")),
    @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
    @tactics.disch_tac,
    @tactics.thenl(
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(thm("label_steps"))(th))),
      @list.List(cases),
    ),
  ])
  // a step inside the label: the induction hypothesis
  let le_suc = arith("∀ k : Num, ∀ n : Num, k <= n → k <= SUC(n)")
  let le_n_suc = arith("∀ n : Num, n <= SUC(n)")
  let inside = seq([
    subst_vars(),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.exists_tac(tm("(qb : \{assn})")),
    @tactics.exists_tac(tm("(lb : \{assn})")),
    @meson.asm_meson_tac(ths([le_suc])),
  ])
  let not_vals = seq([subst_vars(), @meson.asm_meson_tac(ths([thm("br_not_vals"), @wasm.thm("all_vals_map")]))])
  let not_trap = seq([subst_vars(), @meson.asm_meson_tac(ths([thm("br_not_trap")]))])
  let map_trap = [@wasm.thm("map_v_to_e_eq_cons"), @wasm.thm("eq_v_to_e"), einstr_d, @equal.gsym(einstr_d)]
  let arith_suc = arith("∀ i : Num, ∀ d : Num, SUC(i) + d == i + (d + 1)")
  let arith_ne = arith("∀ i : Num, ∀ d : Num, !(d == SUC(i) + d)")
  let _ = lemma(
    "label_safe",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ m : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ qb : \{assn}, ∀ lb : \{assn}, ∀ q : \{assn}, ∀ l : List[\{assn}], safel(n, s, f, li, qb, CONS(lb, l)) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], qb(s, f, vs) → q(s, f, APPEND(vs0, vs))) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ k : Num, k <= n → lb(s, f, vs) → LENGTH(vs) == m && safel(k, s, f, APPEND(MAP(v_to_e, vs0), APPEND(MAP(v_to_e, vs), e0)), q, l)) → safel(n, s, f, APPEND(MAP(v_to_e, vs0), [\{label}]), q, l)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.conv_tac(
            @equal.rator_conv(@equal.rand_conv(@equal.rator_conv(@equal.rand_conv(@simp.pure_once_rewrite_conv(ths([safel])))))),
          ),
          @tactics.thenl(
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            @list.List([
              // the body has ended with values vs: they leave the label
              seq([
                subst_vars(),
                @simp.rewrite_tac(ths([safel])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    base_step(
                      "[Label((m : Num), (e0 : List[Einstr]), MAP(v_to_e, (vs : List[Value])))]",
                      "MAP(v_to_e, (vs : List[Value]))",
                      @tactics.match_accept_tac(rs[27]),
                    ),
                    steps([
                      @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_vals")])),
                      seq([
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("map_v_to_e_inj")]))),
                        subst_vars(),
                        @simp.rewrite_tac(ths([@equal.gsym(@lists.map_append())])),
                        @tactics.match_mp_tac(thm("safel_vals")),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths(map_trap))),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      seq([
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfilled_eq]))),
                        @meson.asm_meson_tac(ths([thm("br_not_vals"), @wasm.thm("all_vals_map")])),
                      ]),
                    ]),
                  ]),
                ),
              ]),
              // the body stopped at a br to label i
              @tactics.thenl(
                @tactics.disj_cases_tac(@bool.spec(tm("(i : Num)"), @nums.num_cases())),
                @list.List([
                  // to this label: the label takes the br
                  seq([
                    subst_vars(),
                    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.el(), @lists.hd(), @arith.add_clauses()]))),
                    @simp.rewrite_tac(ths([safel, @arith.add_clauses()])),
                    @tactics.disj2_tac,
                    @tactics.disj2_tac,
                    have("LENGTH((vs : List[Value])) == (m : Num)", @meson.asm_meson_tac(ths([le_n_suc]))),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([
                          base_step(
                            "[Label((m : Num), (e0 : List[Einstr]), lfill((lh : Lholed), APPEND(MAP(v_to_e, (vs : List[Value])), [Basic(Br(lh_depth(lh)))])))]",
                            "APPEND(MAP(v_to_e, (vs : List[Value])), (e0 : List[Einstr]))",
                            seq([
                              @tactics.match_mp_tac(rs[29]),
                              @tactics.exists_tac(tm("(lh : Lholed)")),
                              @tactics.exists_tac(tm("lh_depth((lh : Lholed))")),
                              @simp.asm_rewrite_tac(ths([@wasm.thm("lfilled_lfill")])),
                            ]),
                          ),
                        ]),
                        steps([
                          inside,
                          not_vals,
                          not_trap,
                          seq([
                            @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfilled_eq]))),
                            subst_vars(),
                            have(
                              "(vs' : List[Value]) == (vs : List[Value])",
                              @meson.asm_meson_tac(ths([thm("br_unique")])),
                            ),
                            subst_vars(),
                            @meson.asm_meson_tac(ths([le_n_suc])),
                          ]),
                        ]),
                      ]),
                    ),
                  ]),
                  // to a label outside: so does the labelled configuration
                  seq([
                    @tactics.first_x_assum(th => @tactics.x_choose_tac(tm("(i1 : Num)"), th)),
                    subst_vars(),
                    @simp.rewrite_tac(ths([safel])),
                    @tactics.disj2_tac,
                    @tactics.disj1_tac,
                    @tactics.exists_tac(tm("(i1 : Num)")),
                    @tactics.exists_tac(tm("(vs : List[Value])")),
                    @tactics.exists_tac(tm("LRec(\{vs0}, (m : Num), (e0 : List[Einstr]), (lh : Lholed), NIL)")),
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(ths([@lists.el(), @lists.tl(), @lists.length(), @arith.lt_suc()])),
                    ),
                    @tactics.repeat_tac(@tactics.conj_tac),
                    @tactics.first(@list.List([
                      solve(@simp.asm_rewrite_tac(ths([lfill, depth, arith_suc]))),
                      steps([
                        inside,
                        not_vals,
                        not_trap,
                        seq([
                          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfilled_eq]))),
                          subst_vars(),
                          @meson.asm_meson_tac(ths([thm("br_unique"), arith_ne])),
                        ]),
                      ]),
                    ])),
                  ]),
                ]),
              ),
              // the body steps
              seq([
                @simp.rewrite_tac(ths([safel])),
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    @meson.asm_meson_tac(ths([thm("reduce_label")])),
                    steps([
                      inside,
                      seq([subst_vars(), @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_vals")]))]),
                      seq([subst_vars(), @meson.asm_meson_tac(ths([@wasm.thm("reduce_not_trap")]))]),
                      seq([
                        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfilled_eq]))),
                        subst_vars(),
                        @meson.asm_meson_tac(ths([thm("br_stuck"), @arith.le_refl()])),
                      ]),
                    ]),
                  ]),
                ),
              ]),
            ]),
          ),
        ]),
      ]),
    ),
  )
}

///|
/// The rule for blocks with no parameters (block types Tbv(ot)).
fn prove_block_rule() -> Unit raise {
  def(
    "tbv_results",
    "tbv_results((NONE : Option[Valtype])) == (NIL : List[Valtype]) && tbv_results(SOME(t)) == [t]",
  )
  let tb_tf_tbv = lemma(
    "tb_tf_tbv",
    "∀ i : Inst, ∀ ot : Option[Valtype], tb_tf(i, Tbv(ot)) == Tf(NIL, tbv_results(ot))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.struct_cases_tac(@bool.ispec(tm("(ot : Option[Valtype])"), @ind_types.cases("option"))),
      @simp.rewrite_tac(ths([@wasm.thm("tb_tf"), thm("tbv_results")])),
    ]),
  )
  let block = "Basic(Block(Tbv((ot : Option[Valtype])), (bs : List[B_e])))"
  let simple = @bool.gen_all(
    prove_arity(
      "arity_simple_block",
      "reduce_simple",
      "∀ suf : List[Einstr], ∀ e2 : List[Einstr], reduce_simple(APPEND(suf, [\{block}]), e2) && ALL(is_val, suf) → LENGTH(suf) == 0",
      [thm("no_trap")],
    ),
  )
  let arity = prove_arity(
    "arity_block",
    "reduce_base",
    "∀ s : Wstore, ∀ f : Wframe, ∀ suf : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ e2 : List[Einstr], reduce_base(s, f, APPEND(suf, [\{block}]), s2, f2, e2) && ALL(is_val, suf) → LENGTH(suf) == 0",
    [simple, tb_tf_tbv, @ind_types.injectivity("tf"), @lists.length_map(), @lists.length()],
  )
  let prefix = @bool.gen_all(prove_prefix("block", [], block, arity))
  let s_ = tm("(s : Wstore)")
  let f_ = tm("(f : Wframe)")
  let cases = @wasm.step_cases(s_, f_, tm("[\{block}]"), compute=false)
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let lists = [@lists.map(), @lists.append(), @lists.append_nil()]
  let enter = "[Label(LENGTH(tbv_results((ot : Option[Valtype]))), NIL, MAP(Basic, (bs : List[B_e])))]"
  let vs0 = "(vs0 : List[Value])"
  let block_step = lemma(
    "block_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ ot : Option[Valtype], ∀ bs : List[B_e], reduce(s, f, APPEND(MAP(v_to_e, vs0), [\{block}]), s, f, APPEND(MAP(v_to_e, vs0), \{enter}))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      have(
        "reduce_base((s : Wstore), (f : Wframe), APPEND(MAP(v_to_e, (NIL : List[Value])), [\{block}]), s, f, [Label(LENGTH(tbv_results((ot : Option[Valtype]))), NIL, APPEND(MAP(v_to_e, (NIL : List[Value])), MAP(Basic, (bs : List[B_e]))))])",
        seq([
          @tactics.match_mp_tac(rb[36]),
          @simp.rewrite_tac(ths([tb_tf_tbv, @ind_types.injectivity("tf"), @lists.length()])),
          @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
          @simp.rewrite_tac(ths([@lists.length()])),
        ]),
      ),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(@wasm.thm("decomp_reduce"))(th))),
      @tactics.disch_then(th => @tactics.mp_tac(@bool.ispec(tm("LBase(\{vs0}, NIL)"), th))),
      @simp.rewrite_tac(ths([@wasm.thm("lfill")] + lists)),
    ]),
  )
  let star = thm("star")
  let star_some = lemma(
    "star_some",
    "∀ p : \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, star(p, r, h) → (∃ h1 : \{heap}, p(h1))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  let lift = thm("lift")
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == vs0 && pb(NIL, lc, gs, ms, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ r : List[Value], vs == APPEND(vs0, r) && (qb(r, lc, gs, ms, h) || lb(r, lc, gs, ms, h)))"
  let sa = "\{sassn}"
  // the post of the block from the body's values (or a br)
  let from_body = (which : String) => seq([
    @tactics.match_mp_tac(thm("lift_mono")),
    @tactics.exists_tac(tm("(\{which} : \{sa})")),
    @tactics.exists_tac(tm("(vs : List[Value])")),
    @simp.asm_rewrite_tac(ths([])),
    @meson.meson_tac(ths([])),
  ])
  let _ = lemma(
    "sl_block",
    "∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ pb : \{sa}, ∀ qb : \{sa}, ∀ lb : \{sa}, ∀ ls : List[\{sa}], ∀ vs0 : List[Value], (∀ r : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, lb(r, lc, gs, ms, h) → LENGTH(r) == LENGTH(tbv_results(ot))) && sl_triple_l(pb, bs, qb, CONS(lb, ls)) → sl_triple_l(\{pre}, [Block(Tbv(ot), bs)], \{post}, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_l"), thm("triple_l")])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.x_gen_tac(tm("(fr : \{hprop})")),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths(lists)),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safel")])),
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          @meson.meson_tac(ths([block_step])),
          seq([
            @tactics.x_gen_tac(tm("(t1 : Wstore)")),
            @tactics.x_gen_tac(tm("(t2 : Wframe)")),
            @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
            @tactics.disch_tac,
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.rewrite_tac(ths([tb_tf_tbv, @ind_types.injectivity("tf")] + lists)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @tactics.match_mp_tac(thm("label_safe")),
            @tactics.exists_tac(tm("lift((qb : \{sa}), (fr : \{hprop}))")),
            @tactics.exists_tac(tm("lift((lb : \{sa}), (fr : \{hprop}))")),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                // the body is safe: its triple, from an empty stack
                seq([
                  @tactics.first_x_assum(th => @tactics.mp_tac(
                    @bool.ispecl(@list.List([tm("(fr : \{hprop})"), s_, f_, tm("(NIL : List[Value])"), tm("(n' : Num)")]), th),
                  )),
                  @simp.rewrite_tac(ths(lists + [lift])),
                  @meson.asm_meson_tac(ths([])),
                ]),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    seq([@tactics.repeat_tac(@tactics.strip_tac), from_body("qb")]),
                    seq([
                      @tactics.repeat_tac(@tactics.gen_tac),
                      @tactics.disch_tac,
                      @tactics.disch_tac,
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          // a br to the block has its arity
                          seq([
                            @tactics.first_x_assum(th => @tactics.mp_tac(th)),
                            @simp.rewrite_tac(ths([lift])),
                            @tactics.repeat_tac(@tactics.strip_tac),
                            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(star_some)(th))),
                            @meson.asm_meson_tac(ths([])),
                          ]),
                          seq([
                            @simp.rewrite_tac(ths([@lists.append_nil(), @equal.gsym(@lists.map_append())])),
                            @tactics.match_mp_tac(thm("safel_vals")),
                            from_body("lb"),
                          ]),
                        ]),
                      ),
                    ]),
                  ]),
                ),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}
