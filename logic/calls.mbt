// Calls.
//
// A call's meaning depends on the store's function table, which the
// triples so far do not see: they hold for every store. Calls are verified
// with module triples (sl_triple_m), triples for the stores whose function
// table is a given fs, run in a given instance. Code without calls keeps
// the table and the instance (call_free_step), so every triple so far
// carries over to module triples for call-free code.
//
// - has_call_b, has_call: a basic instruction, or an instruction, holds a
//   call (call or call_indirect, at any depth), and for instructions also
//   an Invoke or a Frame (they only come from calls); call_free(es): no
//   instruction of es does.
// - call_free_step: a step of call-free code keeps the store's functions
//   and the frame's instance, and leaves call-free code.

///|
/// An inductive relation `name` (as package wasm's `inductive`): its
/// rules, induction and cases theorems are recorded as name_rules,
/// name_induct and name_cases.
#callsite(autofill(loc))
fn inductive_def(name : String, rels : Array[(String, String)], rules : Array[String], loc~ : SourceLoc) -> Unit raise {
  let binders = rels.map(r => "(\{r.0} : \{r.1}) => ").join("")
  let clauses = []
  for r in rules {
    let parsed = tm(binders + "(" + r + ")")
    let (relvars, body) = @basics.strip_abs(parsed)
    let fvs = @kernel.frees(body).filter(v => !relvars.iter().any(w => w == v))
    clauses.push(@bool.list_mk_forall(fvs, body))
  }
  let spec = @bool.list_mk_conj(@list.List(clauses))
  let (rules, induct, cases) = @ind_defs.new_inductive_definition(spec) catch {
    e => raise Failure("wasmcert/logic: defining " + name + ": " + e.to_string())
  }
  record(name + "_rules", rules, kind="definition", loc~)
  record(name + "_induct", induct, loc~)
  record(name + "_cases", cases, loc~)
}

///|
/// The constructors' distinctness and injectivity, both ways.
fn calls_ctor_facts() -> Array[@kernel.Thm] raise {
  let out = []
  for t in ["einstr", "b_e", "value", "lholed"] {
    let d = @ind_types.distinctness(t)
    out.push(d)
    out.push(@equal.gsym(d))
    out.push(@ind_types.injectivity(t))
  }
  out
}

///|
/// has_call_b(C(...)) and has_call(C(...)) for a constructor C, written
/// out: the cases theorem, once, and the constructors compared.
fn has_call_conv() -> @equal.Conv raise {
  let b_eq = thm("has_call_b_eq")
  let e_eq = thm("has_call_eq")
  let rws = @simp.rewrite_conv(ths(calls_ctor_facts()))
  let unwind = @equal.top_depth_conv(@ind_types.unwind_conv)
  t => {
    let (f, args) = @basics.strip_comb(t)
    guard f is Const(name, _) && (name == "has_call_b" || name == "has_call") &&
      args.to_array() is [arg] &&
      @basics.strip_comb(arg).0 is Const(c, _) &&
      c.length() > 0 &&
      c[0] >= 'A' &&
      c[0] <= 'Z' else {
      raise Failure("has_call_conv")
    }
    let eq = if name == "has_call_b" { b_eq } else { e_eq }
    @equal.thenc(@simp.rewr_conv(eq), @equal.thenc(rws, @equal.try_conv(unwind)))(t)
  }
}

///|
fn prove_calls() -> Unit raise {
  prove_call_free()
  prove_call_free_step()
  prove_call_free_steps()
  prove_module_triples()
}

///|
fn prove_call_free() -> Unit raise {
  inductive_def("has_call_b", [("has_call_b", "(B_e) -> Bool")], [
    "has_call_b(Call(j))",
    "has_call_b(Call_indirect(t, j))",
    "MEM(b, bs) && has_call_b(b) → has_call_b(Block(tb, bs))",
    "MEM(b, bs) && has_call_b(b) → has_call_b(Loop(tb, bs))",
    "MEM(b, bs1) && has_call_b(b) → has_call_b(If(tb, bs1, bs2))",
    "MEM(b, bs2) && has_call_b(b) → has_call_b(If(tb, bs1, bs2))",
  ])
  inductive_def("has_call", [("has_call", "(Einstr) -> Bool")], [
    "has_call_b(b) → has_call(Basic(b))",
    "has_call(Invoke(a))",
    "has_call(Frame(n, f, es))",
    "MEM(e, es) && has_call(e) → has_call(Label(n, es, les))",
    "MEM(e, les) && has_call(e) → has_call(Label(n, es, les))",
  ])
  def("call_free", "call_free(es) == ALL((e : Einstr) => !has_call(e), es)")
  def("call_free_b", "call_free_b(bs) == ALL((b : B_e) => !has_call_b(b), bs)")
  let ex_mem = @equal.gsym(@lists.ex_mem())
  let _ = lemma(
    "has_call_b_eq",
    "∀ b : B_e, has_call_b(b) == ((∃ j : Num, b == Call(j)) || (∃ t : Num, ∃ j : Num, b == Call_indirect(t, j)) || (∃ tb : Tb, ∃ bs : List[B_e], b == Block(tb, bs) && EX(has_call_b, bs)) || (∃ tb : Tb, ∃ bs : List[B_e], b == Loop(tb, bs) && EX(has_call_b, bs)) || (∃ tb : Tb, ∃ bs1 : List[B_e], ∃ bs2 : List[B_e], b == If(tb, bs1, bs2) && (EX(has_call_b, bs1) || EX(has_call_b, bs2))))",
    seq([
      @tactics.gen_tac,
      @tactics.conv_tac(@equal.rator_conv(@equal.rand_conv(@simp.rewr_conv(thm("has_call_b_cases"))))),
      @simp.rewrite_tac(ths([ex_mem])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "has_call_eq",
    "∀ e : Einstr, has_call(e) == ((∃ b : B_e, e == Basic(b) && has_call_b(b)) || (∃ a : Num, e == Invoke(a)) || (∃ n : Num, ∃ f : Wframe, ∃ es : List[Einstr], e == Frame(n, f, es)) || (∃ n : Num, ∃ es : List[Einstr], ∃ les : List[Einstr], e == Label(n, es, les) && (EX(has_call, es) || EX(has_call, les))))",
    seq([
      @tactics.gen_tac,
      @tactics.conv_tac(@equal.rator_conv(@equal.rand_conv(@simp.rewr_conv(thm("has_call_cases"))))),
      @simp.rewrite_tac(ths([ex_mem])),
      @meson.meson_tac(ths([])),
    ]),
  )
}

///|
/// Steps of call-free code keep the functions and the instance.
fn prove_call_free_step() -> Unit raise {
  let cf = thm("call_free")
  let not_ex = @lists.not_ex()
  let hc = @tactics.conv_tac(@equal.top_depth_conv(has_call_conv()))
  let lists = [cf, @lists.all(), @lists.all_append(), @lists.map(), @lists.append(), @lists.append_nil(), not_ex]
  let _ = lemma(
    "call_free_vals",
    "∀ vs : List[Value], call_free(MAP(v_to_e, vs))",
    seq([
      @lists.list_induct_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([cf]))),
      @simp.rewrite_tac(ths(lists)),
      @tactics.struct_cases_tac(@bool.ispec(tm("(h : Value)"), @ind_types.cases("value"))),
      @simp.rewrite_tac(ths([@wasm.thm("v_to_e")])),
      hc,
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "call_free_basic",
    "∀ bs : List[B_e], call_free(MAP(Basic, bs)) == call_free_b(bs)",
    seq([
      @lists.list_induct_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([cf, thm("call_free_b")]))),
      @simp.rewrite_tac(ths(lists + [thm("call_free_b")])),
      hc,
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let lfill = @wasm.thm("lfill")
  let vals = @simp.rewrite_rule(ths([cf]))(thm("call_free_vals"))
  let _ = lemma(
    "call_free_lfill_nil",
    "∀ lh : Lholed, ∀ es : List[Einstr], call_free(lfill(lh, es)) == (call_free(lfill(lh, NIL)) && call_free(es))",
    seq([
      @tactics.match_mp_tac(@wasm.thm("lholed_induct")),
      @simp.rewrite_tac(ths([lfill] + lists)),
      hc,
      @simp.rewrite_tac(ths(lists + [vals, @class.de_morgan_thm()])),
      @tactics.repeat_tac(@tactics.strip_tac),
      // the hypothesis's right side matches its left: rewrite with it once
      @tactics.try_tac(@tactics.first_x_assum(th => @simp.once_rewrite_tac(ths([th])))),
      @simp.rewrite_tac(ths([@lists.all()])),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  // the context's part, named so that rewriting with it stops
  def("call_free_ctx", "call_free_ctx(lh) == call_free(lfill(lh, NIL))")
  let _ = lemma(
    "call_free_lfill",
    "∀ lh : Lholed, ∀ es : List[Einstr], call_free(lfill(lh, es)) == (call_free_ctx(lh) && call_free(es))",
    seq([@simp.rewrite_tac(ths([thm("call_free_ctx")])), @tactics.match_accept_tac(thm("call_free_lfill_nil"))]),
  )
  let _ = lemma(
    "no_call_v_to_e",
    "∀ v : Value, !has_call(v_to_e(v))",
    seq([
      @tactics.gen_tac,
      @tactics.struct_cases_tac(@bool.ispec(tm("(v : Value)"), @ind_types.cases("value"))),
      @simp.rewrite_tac(ths([@wasm.thm("v_to_e")])),
      hc,
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "s_funcs_updates",
    "s_funcs(s_tabs_update(v1, (s : Wstore))) == s_funcs(s) && s_funcs(s_mems_update(v2, s)) == s_funcs(s) && s_funcs(s_globs_update(v3, s)) == s_funcs(s) && s_funcs(s_elems_update(v4, s)) == s_funcs(s) && s_funcs(s_datas_update(v5, s)) == s_funcs(s)",
    seq([
      @tactics.struct_cases_tac(@bool.ispec(tm("(s : Wstore)"), @ind_types.cases("wstore"))),
      @simp.rewrite_tac(
        ths(
          ["s_funcs", "s_tabs_update", "s_mems_update", "s_globs_update", "s_elems_update", "s_datas_update"].map(
            n => @wasm.thm(n),
          ),
        ),
      ),
    ]),
  )
}

///|
/// The rewrites that decide call_free of written-out code: unfolded, with
/// values, MAP(Basic, ...) and contexts.
fn call_free_rws() -> Array[@kernel.Thm] raise {
  let cf = thm("call_free")
  let unfold = @simp.rewrite_rule(ths([cf, thm("call_free_b")]))
  [
    cf,
    @lists.all(),
    @lists.all_append(),
    @lists.map(),
    @lists.append(),
    @lists.append_nil(),
    @lists.not_ex(),
    @class.de_morgan_thm(),
    unfold(thm("call_free_vals")),
    unfold(thm("call_free_basic")),
    unfold(thm("call_free_lfill")),
    thm("no_call_v_to_e"),
  ]
}

///|
/// Steps of call-free code: reduce_simple, then reduce.
fn prove_call_free_steps() -> Unit raise {
  let hc = @tactics.conv_tac(@equal.top_depth_conv(has_call_conv()))
  let lfilled = @wasm.thm("lfilled_eq")
  let rws = call_free_rws() + [lfilled]
  let unfold = @simp.rewrite_rule(ths([thm("call_free")]))
  let finish = (extra : Array[@kernel.Thm], lemmas : Array[@kernel.Thm]) => seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths(rws + extra)),
    hc,
    @simp.rewrite_tac(ths(rws + extra)),
    // unfolding can expose more instructions to decide
    hc,
    @simp.rewrite_tac(ths(rws + extra)),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths(rws + extra)),
    @tactics.try_tac(@meson.asm_meson_tac(ths(lemmas))),
  ])
  let simple = lemma(
    "simple_call_free",
    "∀ es : List[Einstr], ∀ es2 : List[Einstr], reduce_simple(es, es2) → call_free(es) → call_free(es2)",
    seq([@tactics.match_mp_tac(@wasm.thm("reduce_simple_induct")), finish([], [])]),
  )
  let _ = lemma(
    "call_free_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → call_free(es) → s_funcs(s2) == s_funcs(s) && f_inst(f2) == f_inst(f) && call_free(es2)",
    seq([
      @tactics.match_mp_tac(@wasm.thm("reduce_induct")),
      finish(
        [thm("s_funcs_updates"), @wasm.thm("f_inst"), @wasm.thm("supdate_glob")],
        [unfold(simple), unfold(thm("call_free_lfill"))],
      ),
    ]),
  )
}

///|
/// Module triples: the store's functions are fs and the frame's instance
/// inst, before and after (keep), and every triple of call-free code is
/// one (sl_triple_m_of).
fn prove_module_triples() -> Unit raise {
  let a = assn
  let sa = sassn
  def(
    "keep",
    "keep((fs : List[Cl]), (inst : Inst), (q : \{a}), (s : Wstore), (f : Wframe), (vs : List[Value])) == (s_funcs(s) == fs && f_inst(f) == inst && q(s, f, vs))",
  )
  def(
    "sl_triple_m",
    "sl_triple_m((fs : List[Cl]), (inst : Inst), (p : \{sa}), (bs : List[B_e]), (q : \{sa}), (ls : List[\{sa}])) == (∀ r : \{hprop}, triple_l(keep(fs, inst, lift(p, r)), bs, keep(fs, inst, lift(q, r)), MAP(keep(fs, inst), MAP((x : \{sa}) => lift(x, r), ls))))",
  )
  let safel = thm("safel")
  let keep = thm("keep")
  let step = thm("call_free_step")
  // a step from here: the next state is in the module, and call-free
  let steps = seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.first_assum(th => @tactics.mp_tac(@drule.match_mp(step)(th))),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.first_assum(th => @tactics.accept_tac(th)),
  ])
  let _ = lemma(
    "safel_keep",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ l : List[\{a}], ∀ fs : List[Cl], ∀ inst : Inst, s_funcs(s) == fs && f_inst(f) == inst && call_free(es) && safel(n, s, f, es, q, l) → safel(n, s, f, es, keep(fs, inst, q), MAP(keep(fs, inst), l))",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safel])),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @simp.rewrite_tac(ths([safel])),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          subst_vars(),
          @tactics.first(@list.List([
            // values
            solve(seq([
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @simp.asm_rewrite_tac(ths([keep])),
            ])),
            // a br out
            solve(seq([
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(i : Num)")),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(tm("(lh : Lholed)")),
              @simp.asm_simp_tac(ths([@lists.length_map(), @lists.el_map(), keep])),
              steps,
            ])),
            // a step
            solve(seq([
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  // the step the hypothesis named
                  seq([
                    @tactics.exists_tac(tm("(s2 : Wstore)")),
                    @tactics.exists_tac(tm("(f2 : Wframe)")),
                    @tactics.exists_tac(tm("(es2 : List[Einstr])")),
                    @tactics.first_assum(th => @tactics.accept_tac(th)),
                  ]),
                  steps,
                ]),
              ),
            ])),
          ])),
        ]),
      ]),
    ),
  )
  let unfold = @simp.rewrite_rule(ths([thm("call_free"), thm("call_free_b")]))
  let _ = lemma(
    "sl_triple_m_of",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], call_free_b(bs) && sl_triple_l(p, bs, q, ls) → sl_triple_m(fs, inst, p, bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple_m"), thm("sl_triple_l"), thm("triple_l"), keep])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safel_keep")),
      @simp.asm_rewrite_tac(
        ths([thm("call_free"), @lists.all_append(), unfold(thm("call_free_vals")), unfold(thm("call_free_basic"))]),
      ),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("call_free_b")]))),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ]),
  )
  let _ = lemma(
    "sl_seq_m",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sa}, ∀ bs1 : List[B_e], ∀ q : \{sa}, ∀ bs2 : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], sl_triple_m(fs, inst, p, bs1, q, ls) && sl_triple_m(fs, inst, q, bs2, r, ls) → sl_triple_m(fs, inst, p, APPEND(bs1, bs2), r, ls)",
    seq([@simp.rewrite_tac(ths([thm("sl_triple_m")])), @meson.meson_tac(ths([thm("triple_l_seq")]))]),
  )
  let ent = (x : String, y : String) => "(∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{x}(vs, lc, gs, ms, h) → \{y}(vs, lc, gs, ms, h))"
  let _ = lemma(
    "sl_conseq_m",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sa}, ∀ p2 : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ q2 : \{sa}, ∀ ls : List[\{sa}], \{ent("p2", "p")} && sl_triple_m(fs, inst, p, bs, q, ls) && \{ent("q", "q2")} → sl_triple_m(fs, inst, p2, bs, q2, ls)",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple_m")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("triple_l_conseq")),
      @tactics.exists_tac(tm("keep(fs, inst, lift((p : \{sa}), (r : \{hprop})))")),
      @tactics.exists_tac(tm("keep(fs, inst, lift((q : \{sa}), (r : \{hprop})))")),
      @tactics.exists_tac(tm("MAP(keep(fs, inst), MAP((x : \{sa}) => lift(x, (r : \{hprop})), (ls : List[\{sa}])))")),
      @simp.asm_rewrite_tac(ths([keep])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(thm("lift_mono")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}
