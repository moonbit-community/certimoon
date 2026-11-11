// Indirect calls.
//
// call_indirect(ti, j) pops an index c and calls the function that table
// ti of the instance holds at c, if its type is the instance's type j;
// otherwise it traps. Module triples keep the store's tables (keep: no
// call-free code writes them, calls.mbt), so a triple can name the tables,
// tabs, and the function c selects.
//
// - call_indirect_step, call_indirect_can_step: when table ti holds the
//   function a at c, and a has type j, the only step is to Invoke(a).
// - sl_call_indirect_g: the call rule for g triples (specs.mbt): with
//   tabs holding a at c and a spec G(a, P, Q), call_indirect runs as a
//   call of a with that spec.
// - sl_call_indirect_st_g: the same as sym_prove uses it (sym.mbt): the
//   arguments and c on top of the stack of an exact state.

///|
/// The table of `inst` numbered `ti`, in `tabs`, holds the function a at
/// `c`, and a's type in `fs` is the instance's type j.
fn table_holds(tabs : String, fs : String, inst : String, c : String) -> String {
  "ti < LENGTH(inst_tabs(\{inst})) && tab_cl_ind(\{tabs}, EL(ti, inst_tabs(\{inst})), val(\{c})) == SOME(ConstRefFunc(a)) && cl_type(EL(a, \{fs})) == stypes(\{inst}, j)"
}

///|
fn prove_call_indirect_steps() -> Unit raise {
  let w = w32
  let c = "Basic(EConstNum(ConstInt32((c : \{w}))))"
  let x = "Basic(Call_indirect((ti : Num), (j : Num)))"
  let arity = prove_arities("call_indirect", x, 1)
  let prefix = @bool.gen_all(prove_prefix("call_indirect", [c], x, arity))
  let cases = @bool.gen_all(step_cases_of(tm("(s : Wstore)"), tm("(f : Wframe)"), "[\{c}, \{x}]"))
  let found = "stab(s, f_inst(f), ti, val(c)) == SOME(ConstRefFunc(a)) && cl_type(EL(a, s_funcs(s))) == stypes(f_inst(f), j)"
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ vs0 : List[Value], ∀ c : \{w}, ∀ ti : Num, ∀ j : Num, ∀ a : Num"
  let code = "APPEND(MAP(v_to_e, vs0), [\{c}, \{x}])"
  let refs = [
    @ind_types.option_inj(),
    @ind_types.injectivity("v_ref"),
    @wasm.thm("is_some_const_ref_func"),
  ]
  let _ = lemma(
    "call_indirect_step",
    "\{vars}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], \{found} && reduce(s, f, \{code}, s2, f2, es2) → s2 == s && f2 == f && es2 == APPEND(MAP(v_to_e, vs0), [Invoke(a)])",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
      @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(cases)(th))),
      subst_vars(),
      // the table's entry is a: the other assumptions about it, rewritten
      // with it, say i_cl is a, or contradict it (the trap's conditions)
      @tactics.first_x_assum(th => {
        let t = @kernel.concl(th)
        if @basics.is_eq(t) &&
          @basics.strip_comb(@equal.lhs(t)).0 is Const("stab", _) &&
          @kernel.rand(@kernel.rand(@equal.rhs(t))) is Var("a", _) {
          seq([@tactics.rule_assum_tac(@simp.rewrite_rule(ths([th]))), @tactics.assume_tac(th)])
        } else {
          @tactics.no_tac
        }
      }),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(refs))),
      subst_vars(),
      @simp.asm_rewrite_tac(ths(refs)),
      @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
    ]),
  )
  let rb = @wasm.thm("reduce_base_rules")
  let _ = lemma(
    "call_indirect_can_step",
    "\{vars}, \{found} → reduce(s, f, \{code}, s, f, APPEND(MAP(v_to_e, vs0), [Invoke(a)]))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("reduce_after_vals")),
      @tactics.match_mp_tac(rule_with(rb, ["Call_indirect(", "Invoke(i_cl)"])),
      @tactics.exists_tac(tm("f_inst((f : Wframe))")),
      @tactics.exists_tac(tm("stypes(f_inst((f : Wframe)), (j : Num))")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}

///|
fn prove_call_indirect_g() -> Unit raise {
  let sa = sassn
  let w = w32
  let env = env_vars()
  let cv = "V_num(ConstInt32(c))"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ args : List[Value], vs == APPEND(APPEND(vs0, args), [\{cv}]) && lc == lc0 && P(args, gs, ms, h)"
  let post = call_post("Q", "vs0", "lc0")
  let specs_assum = (ttac : (@kernel.Thm) -> @tactics.Tactic) => {
    @tactics.first_x_assum(th => {
      if @basics.strip_comb(@kernel.concl(th)).0 is Const("specs_ok", _) {
        ttac(th)
      } else {
        @tactics.no_tac
      }
    })
  }
  let keep_assum = (ttac : (@kernel.Thm) -> @tactics.Tactic) => {
    @tactics.first_assum(th => {
      if @basics.strip_comb(@kernel.concl(th)).0 is Const("keep", _) {
        ttac(th)
      } else {
        @tactics.no_tac
      }
    })
  }
  let vs1 = "(vs1 : List[Value])"
  let c_t = "(c : \{w})"
  let found = [thm("in_mod"), @wasm.thm("stab"), @wasm.thm("stab_cl_ind")]
  let _ = lemma(
    "sl_call_indirect_g",
    "\{env}∀ ti : Num, ∀ j : Num, ∀ c : \{w}, ∀ a : Num, ∀ P : \{fprop}, ∀ Q : \{fprop}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], ∀ ls : List[\{sa}], \{table_holds("tabs", "fs", "inst", "c")} && G(a, P, Q) → \{triple_g(pre, "[Call_indirect(ti, j)]", post, "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.rewrite_tac(ths([thm("sl_triple_g"), @lists.map()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      // the stack is the arguments' stack with c on top
      have(
        "∃ vs1 : List[Value], (vs : List[Value]) == APPEND(vs1, [V_num(ConstInt32(\{c_t}))])",
        seq([
          keep_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([thm("keep_in_mod")] + lift_facts())),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.exists_tac(tm("APPEND((vs0 : List[Value]), (args : List[Value]))")),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
      @tactics.first_x_assum(th => @tactics.x_choose_tac(tm(vs1), th)),
      subst_only("vs"),
      // the code: c's instruction, then call_indirect
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), @wasm.thm("v_to_e"), @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      // the module: the instance, functions and tables are inst, fs, tabs
      have(
        "in_mod((fs : List[Cl]), (tabs : List[(Tab_t, List[V_ref])]), (inst : Inst), (s : Wstore), (f : Wframe))",
        seq([
          keep_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([thm("keep_in_mod")])),
          @tactics.disch_then(th => @tactics.accept_tac(@bool.conjunct1(th))),
        ]),
      ),
      cases_n_specs(),
      @simp.rewrite_tac(ths([thm("safer")])),
      safer_steps(
        seq([
          @tactics.exists_tac(tm("(s : Wstore)")),
          @tactics.exists_tac(tm("(f : Wframe)")),
          @tactics.exists_tac(tm("APPEND(MAP(v_to_e, \{vs1}), [Invoke((a : Num))])")),
          @tactics.match_mp_tac(thm("call_indirect_can_step")),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("in_mod")]))),
          @simp.asm_rewrite_tac(ths(found)),
        ]),
        seq([
          @tactics.mp_tac(
            @bool.ispecl(
              @list.List(
                [
                  "(s : Wstore)", "(f : Wframe)", vs1, c_t, "(ti : Num)", "(j : Num)", "(a : Num)",
                  "(s2 : Wstore)", "(f2 : Wframe)", "(es2 : List[Einstr])",
                ].map(tm),
              ),
              thm("call_indirect_step"),
            ),
          ),
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("in_mod")]))),
          @simp.asm_rewrite_tac(ths(found)),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          subst_only("s2"),
          subst_only("f2"),
          subst_only("es2"),
          // the call of a, by its spec
          specs_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([thm("specs_ok"), thm("inv_ok")])),
          @tactics.disch_then(th => {
            @tactics.mp_tac(
              @bool.ispecl(@list.List([tm("(a : Num)"), tm("(P : \{fprop})"), tm("(Q : \{fprop})")]), th),
            )
          }),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.disch_then(th => @tactics.match_mp_tac(th)),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @simp.rewrite_tac(ths([arith("∀ n : Num, n <= SUC(n)")])),
              // the precondition, with c taken off the stack
              seq([
                @tactics.first_assum(th => {
                  if @basics.strip_comb(@kernel.concl(th)).0 is Const("keep", _) {
                    @tactics.mp_tac(th)
                  } else {
                    @tactics.no_tac
                  }
                }),
                @simp.rewrite_tac(ths([thm("keep_in_mod")])),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                @simp.asm_rewrite_tac(ths([])),
                @tactics.match_mp_tac(thm("lift_mono")),
                @tactics.exists_tac(tm(pre)),
                @tactics.exists_tac(tm("APPEND(\{vs1}, [V_num(ConstInt32(\{c_t}))])")),
                @simp.asm_rewrite_tac(ths([@lists.append_rcancel()])),
                @tactics.repeat_tac(@tactics.strip_tac),
                @tactics.exists_tac(tm("(args : List[Value])")),
                @simp.asm_rewrite_tac(ths([])),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  // as sym_prove takes it (sl_call_st_g): the arguments ain and c on top
  // of an exact state's stack, a spec whose Q gives the results aout, and
  // the code after the call starting from them
  let st = thm("st")
  let cons_append = @equal.gsym(
    @simp.rewrite_conv(ths([@lists.append()]))(tm("APPEND([Call_indirect((ti : Num), (j : Num))], (rest : List[B_e]))")),
  )
  let q = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == aout && Rout(gs, ms, h)"
  let after = "st(APPEND(v0, aout), l, Rout)"
  let pre_v0 = pre.replace_all(old="vs0", new="v0").replace_all(old="lc0", new="l")
  // the exact state is the call's precondition, with args ain
  let to_pre = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([st])),
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.exists_tac(tm("(ain : List[Value])")),
    @simp.asm_rewrite_tac(ths([@lists.append_assoc()])),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([st])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let _ = lemma(
    "sl_call_indirect_st_g",
    "\{env}∀ ti : Num, ∀ j : Num, ∀ c : \{w}, ∀ a : Num, ∀ P : \{fprop}, ∀ aout : List[Value], ∀ Rout : \{rty}, ∀ v0 : List[Value], ∀ ain : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], G(a, P, \{q}) → (\{table_holds("tabs", "fs", "inst", "c")} && (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → P(ain, gs, ms, h))) && \{triple_g(after, "rest", "r", "ls")} → \{triple_g("st(APPEND(v0, APPEND(ain, [\{cv}])), l, R)", "CONS(Call_indirect(ti, j), rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.subst1_tac(cons_append),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(tm(after)),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(tm(pre_v0)),
      @tactics.exists_tac(tm(call_post("(\{q})", "v0", "l"))),
      @tactics.exists_tac(tm("(ls : List[\{sa}])")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.match_mp_tac(thm("sl_call_indirect_g")),
              @tactics.exists_tac(tm("(a : Num)")),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          solve(to_pre),
          solve(simple),
        ]),
      ),
    ]),
  )
}
