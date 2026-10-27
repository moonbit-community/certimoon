// Facts about reduction, the base of the program logic:
//
// - values and [Trap] do not step (reduce_not_vals, reduce_not_trap);
// - evaluation contexts as a function: Lfilled(k, lh, es, les) is
//   k = lh_depth(lh) && les = lfill(lh, es) (lfilled_eq), so Lfilled is
//   deterministic and contexts compose (lfill_compose);
// - reduce is a base step (reduce_base: every rule but the context rule)
//   inside a context (reduce_decompose);
// - a step of APPEND(es1, es2) with es1 not all values is a step of es1,
//   or es1 has a trap at the top (reduce_append);
// - `step_cases`, an inversion procedure: what a basic instruction with
//   its operands can step to.
//
// They are proved on first use (`props`) and recorded like the
// definitions (`thm("reduce_decompose")`).

///|
let trace_props : Ref[Bool] = Ref::{ val: false }

///|
let props_loaded : Ref[Bool] = Ref::{ val: false }

///|
/// Proves the facts about reduction (once).
pub fn props() -> Unit raise {
  if props_loaded.val {
    return
  }
  load()
  props_loaded.val = true
  define_props()
  prove_values()
  prove_lfill()
  prove_not_steps()
  prove_decompose()
  prove_lists()
  prove_shapes()
  prove_append()
  prove_step_basic()
  prove_inversion_lemmas()
}

// Proof helpers.

///|
fn lemma(name : String, stmt : String, tac : @tactics.Tactic) -> @kernel.Thm raise {
  if trace_props.val {
    println("proving " + name)
  }
  // when tracing, show the goals a failing proof leaves
  let tac = if trace_props.val {
    @tactics.then_tac(tac, @tactics.print_goal_tac)
  } else {
    tac
  }
  let th = @tactics.prove(tm(stmt), tac) catch {
    e => raise Failure("wasmcert/wasm: proving " + name + ": " + e.to_string())
  }
  record(name, th)
  th
}

///|
fn seq(tacs : Array[@tactics.Tactic]) -> @tactics.Tactic {
  @tactics.every(@list.List(tacs))
}

///|
fn ths(xs : Array[@kernel.Thm]) -> @list.List[@kernel.Thm] {
  @list.List(xs)
}

///|
let ctor_cache : Ref[Array[@kernel.Thm]?] = Ref::{ val: None }

///|
/// Distinctness (both ways round) and injectivity of the constructors a
/// proof compares, and of lists and options.
fn ctor_facts() -> Array[@kernel.Thm] raise {
  if ctor_cache.val is Some(c) {
    return c
  }
  let out = []
  for t in ["einstr", "b_e", "lholed", "value"] {
    let d = @ind_types.distinctness(t)
    out.push(d)
    out.push(@equal.gsym(d))
    out.push(@ind_types.injectivity(t))
  }
  for th in [@lists.not_cons_nil(), @ind_types.option_distinct()] {
    out.push(th)
    out.push(@equal.gsym(th))
  }
  out.push(@lists.cons_11())
  out.push(@ind_types.option_inj())
  ctor_cache.val = Some(out)
  out
}

///|
/// The i-th rule of relation `rel`.
fn rule_of(rel : String, i : Int) -> @kernel.Thm raise {
  @bool.conjuncts_rule(thm(rel + "_rules")).to_array()[i]
}

///|
/// The position of reduce's context rule among its rules.
let context_rule_index : Int = 38

///|
fn define_props() -> Unit raise {
  def("is_val", "is_val(e) == (∃ v : Value, e == v_to_e(v))")
  def(
    "lfill",
    "lfill(LBase(vs, rest), es) == APPEND(MAP(v_to_e, vs), APPEND(es, rest)) && lfill(LRec(vs, n, e0, l, rest), es) == APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, lfill(l, es)), rest))",
  )
  def(
    "lh_depth",
    "lh_depth(LBase(vs, rest)) == 0 && lh_depth(LRec(vs, n, e0, l, rest)) == lh_depth(l) + 1",
  )
  def(
    "lh_wrap",
    "lh_wrap(vs, rest, LBase(vs2, r2)) == LBase(APPEND(vs, vs2), APPEND(r2, rest)) && lh_wrap(vs, rest, LRec(vs2, n, e0, l, r2)) == LRec(APPEND(vs, vs2), n, e0, l, APPEND(r2, rest))",
  )
  def(
    "lh_compose",
    "lh_compose(LBase(vs, rest), l2) == lh_wrap(vs, rest, l2) && lh_compose(LRec(vs, n, e0, l, rest), l2) == LRec(vs, n, e0, lh_compose(l, l2), rest)",
  )
  // a list that is values then one instruction, or that has a trap at
  // the top after values: the shapes of a base step's left-hand side
  def(
    "last_redex",
    "last_redex(es) == (!(es == NIL) && ALL(is_val, BUTLAST(es)) && !is_val(LAST(es)))",
  )
  def(
    "trap_top",
    "trap_top(es) == (∃ vs : List[Value], ∃ r : List[Einstr], es == APPEND(MAP(v_to_e, vs), CONS(Trap, r)))",
  )
  // reduce without its context rule
  let texts = reduce_rule_texts()
  if !texts[context_rule_index].contains("Lfilled(k, lholed, es', les')") {
    raise Failure("wasmcert/wasm: reduce rule \{context_rule_index} is not the context rule")
  }
  let base = []
  for i, r in texts {
    if i == context_rule_index {
      continue
    }
    // the conclusion follows the arrow, or is the whole rule
    let r2 = if r.contains("→ reduce(") {
      r.replace(old="→ reduce(", new="→ reduce_base(")
    } else if r.has_prefix("reduce(") {
      "reduce_base(" + r.unsafe_substring(start=7, end=r.length())
    } else {
      r
    }
    if !r2.contains("reduce_base(") {
      raise Failure("wasmcert/wasm: no conclusion in reduce rule \{i}")
    }
    base.push(r2)
  }
  inductive("reduce_base", [("reduce_base", reduce_type)], base)
}

///|
fn prove_values() -> Unit raise {
  let is_val_cases = lemma(
    "is_val_cases",
    "∀ e : Einstr, is_val(e) == ((∃ x : V_num, e == Basic(EConstNum(x))) || (∃ y : V_vec, e == Basic(EConstVec(y))) || (∃ r : V_ref, e == Ref(r)))",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([thm("is_val")])),
      @meson.meson_tac(ths([@ind_types.cases("value"), thm("v_to_e")])),
    ]),
  )
  let is_val_basic = lemma(
    "is_val_basic",
    "∀ b : B_e, is_val(Basic(b)) == ((∃ x : V_num, b == EConstNum(x)) || (∃ y : V_vec, b == EConstVec(y)))",
    @simp.rewrite_tac(ths([is_val_cases] + ctor_facts())),
  )
  let _ = lemma(
    "is_val_clauses",
    "(∀ x : V_num, is_val(Basic(EConstNum(x)))) && (∀ y : V_vec, is_val(Basic(EConstVec(y)))) && (∀ r : V_ref, is_val(Ref(r))) && !is_val(Trap) && (∀ i : Num, !is_val(Invoke(i))) && (∀ n : Num, ∀ es : List[Einstr], ∀ les : List[Einstr], !is_val(Label(n, es, les))) && (∀ n : Num, ∀ f : Wframe, ∀ es : List[Einstr], !is_val(Frame(n, f, es))) && (∀ v : Value, is_val(v_to_e(v)))",
    seq([
      @simp.rewrite_tac(ths([is_val_basic, is_val_cases] + ctor_facts())),
      @tactics.try_tac(
        @meson.meson_tac(ths([thm("is_val"), @ind_types.cases("value"), thm("v_to_e")])),
      ),
    ]),
  )
  let _ = lemma(
    "append_eq_sing",
    "∀ l1 : List[A], ∀ l2 : List[A], ∀ x : A, APPEND(l1, l2) == [x] == ((l1 == [x] && l2 == NIL) || (l1 == NIL && l2 == [x]))",
    seq([
      @lists.list_induct_tac,
      @simp.rewrite_tac(ths([@lists.append(), @lists.append_eq_nil()] + ctor_facts())),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let map_cons = lemma(
    "map_v_to_e_cons",
    "∀ h : Einstr, ∀ t : List[Einstr], ∀ vs : List[Value], CONS(h, t) == MAP(v_to_e, vs) == (∃ v : Value, ∃ vs2 : List[Value], vs == CONS(v, vs2) && h == v_to_e(v) && t == MAP(v_to_e, vs2))",
    seq([
      @tactics.gen_tac,
      @tactics.gen_tac,
      @lists.list_induct_tac,
      @simp.rewrite_tac(ths([@lists.map()] + ctor_facts())),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let vals_map = lemma(
    "vals_map",
    "∀ es : List[Einstr], ALL(is_val, es) == (∃ vs : List[Value], es == MAP(v_to_e, vs))",
    seq([
      @lists.list_induct_tac,
      @simp.asm_rewrite_tac(ths([@lists.all(), thm("is_val"), map_cons, @lists.map()] + ctor_facts())),
      @tactics.try_tac(@meson.meson_tac(ths([@lists.map()]))),
    ]),
  )
  let _ = lemma(
    "all_vals_map",
    "∀ vs : List[Value], ALL(is_val, MAP(v_to_e, vs))",
    seq([@simp.rewrite_tac(ths([vals_map])), @meson.meson_tac(ths([]))]),
  )
}

///|
fn prove_lfill() -> Unit raise {
  let lfill = thm("lfill")
  let depth = thm("lh_depth")
  let append = @lists.append()
  let _ = lemma(
    "lfill_nil",
    "∀ es : List[Einstr], lfill(LBase(NIL, NIL), es) == es",
    @simp.rewrite_tac(ths([lfill, @lists.map(), append, @lists.append_nil()])),
  )
  // the rules of Lfilled, with the label written CONS(Label(...), rest)
  let base_rule = lemma(
    "lfilled_base",
    "∀ vs : List[Value], ∀ rest : List[Einstr], ∀ es : List[Einstr], Lfilled(0, LBase(vs, rest), es, APPEND(MAP(v_to_e, vs), APPEND(es, rest)))",
    @meson.meson_tac(ths([thm("Lfilled_rules")])),
  )
  let rec_rule = lemma(
    "lfilled_rec",
    "∀ vs : List[Value], ∀ n : Num, ∀ e0 : List[Einstr], ∀ l : Lholed, ∀ rest : List[Einstr], ∀ k : Num, ∀ es : List[Einstr], ∀ lk : List[Einstr], Lfilled(k, l, es, lk) → Lfilled(k + 1, LRec(vs, n, e0, l, rest), es, APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, lk), rest)))",
    seq([
      @simp.rewrite_tac(ths([])),
      @meson.meson_tac(ths([@simp.rewrite_rule(ths([append]))(thm("Lfilled_rules"))])),
    ]),
  )
  let lfilled_imp = lemma(
    "lfilled_imp",
    "∀ k : Num, ∀ lh : Lholed, ∀ es : List[Einstr], ∀ les : List[Einstr], Lfilled(k, lh, es, les) → k == lh_depth(lh) && les == lfill(lh, es)",
    seq([
      @tactics.match_mp_tac(thm("Lfilled_induct")),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths([depth, lfill, append])),
    ]),
  )
  let lfill_imp = lemma(
    "lfill_imp",
    "∀ lh : Lholed, ∀ k : Num, ∀ es : List[Einstr], ∀ les : List[Einstr], k == lh_depth(lh) && les == lfill(lh, es) → Lfilled(k, lh, es, les)",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(ths([depth, lfill])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths([])),
      @meson.asm_meson_tac(ths([base_rule, rec_rule])),
    ]),
  )
  let lfilled_eq = lemma(
    "lfilled_eq",
    "∀ k : Num, ∀ lh : Lholed, ∀ es : List[Einstr], ∀ les : List[Einstr], Lfilled(k, lh, es, les) == (k == lh_depth(lh) && les == lfill(lh, es))",
    @meson.meson_tac(ths([lfilled_imp, lfill_imp])),
  )
  let _ = lemma(
    "lfilled_lfill",
    "∀ lh : Lholed, ∀ es : List[Einstr], Lfilled(lh_depth(lh), lh, es, lfill(lh, es))",
    @simp.rewrite_tac(ths([lfilled_eq])),
  )
  let _ = lemma(
    "lfilled_deterministic",
    "∀ k : Num, ∀ lh : Lholed, ∀ es : List[Einstr], ∀ l1 : List[Einstr], ∀ l2 : List[Einstr], Lfilled(k, lh, es, l1) && Lfilled(k, lh, es, l2) → l1 == l2",
    seq([@simp.rewrite_tac(ths([lfilled_eq])), @meson.meson_tac(ths([]))]),
  )
  let assoc = [@lists.map_append(), @equal.gsym(@lists.append_assoc()), append]
  let lfill_wrap = lemma(
    "lfill_wrap",
    "∀ vs : List[Value], ∀ rest : List[Einstr], ∀ l : Lholed, ∀ es : List[Einstr], lfill(lh_wrap(vs, rest, l), es) == APPEND(MAP(v_to_e, vs), APPEND(lfill(l, es), rest)) && lh_depth(lh_wrap(vs, rest, l)) == lh_depth(l)",
    seq([
      @tactics.gen_tac,
      @tactics.gen_tac,
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(ths([thm("lh_wrap"), lfill, depth] + assoc)),
    ]),
  )
  let _ = lemma(
    "lfill_compose",
    "∀ lh : Lholed, ∀ l1 : Lholed, ∀ es : List[Einstr], lfill(lh, lfill(l1, es)) == lfill(lh_compose(lh, l1), es) && lh_depth(lh_compose(lh, l1)) == lh_depth(lh) + lh_depth(l1)",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(ths([thm("lh_compose"), lfill, depth, lfill_wrap])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths([@arith.add_ac(), @arith.add_clauses()])),
    ]),
  )
  let all_vals_map = thm("all_vals_map")
  let is_val_clauses = thm("is_val_clauses")
  let _ = lemma(
    "lfill_vals",
    "∀ lh : Lholed, ∀ es : List[Einstr], ALL(is_val, lfill(lh, es)) → ALL(is_val, es)",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(ths([lfill, @lists.all_append(), @lists.all(), is_val_clauses])),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let _ = lemma(
    "lfill_trap",
    "∀ lh : Lholed, ∀ es : List[Einstr], lfill(lh, es) == [Trap] → es == [Trap] || es == NIL",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(
        ths([lfill, thm("append_eq_sing"), @lists.append_eq_nil()] + ctor_facts()),
      ),
      @tactics.try_tac(
        @meson.meson_tac(ths([all_vals_map, @lists.all(), is_val_clauses])),
      ),
    ]),
  )
}

///|
/// The rewrites that decide whether a written-out list is all values or
/// [Trap].
fn val_facts() -> Array[@kernel.Thm] raise {
  [
    @lists.all(),
    @lists.all_append(),
    thm("is_val_clauses"),
    thm("is_val_basic"),
    thm("all_vals_map"),
    thm("append_eq_sing"),
    @lists.append_eq_nil(),
    thm("lfilled_eq"),
  ] +
  ctor_facts()
}

///|
fn prove_not_steps() -> Unit raise {
  let finish = (extra : Array[@kernel.Thm]) => seq([
    @simp.rewrite_tac(ths(val_facts())),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.try_tac(
      @meson.meson_tac(
        ths(
          [thm("lfill_vals"), thm("lfill_trap"), @lists.all(), thm("is_val_clauses")] +
          extra,
        ),
      ),
    ),
  ])
  let simple = lemma(
    "reduce_simple_ok",
    "∀ es : List[Einstr], ∀ es' : List[Einstr], reduce_simple(es, es') → !ALL(is_val, es) && !(es == [Trap])",
    seq([@tactics.match_mp_tac(thm("reduce_simple_induct")), finish([])]),
  )
  let ok = lemma(
    "reduce_ok",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], reduce(s, f, es, s', f', es') → !ALL(is_val, es) && !(es == [Trap])",
    seq([@tactics.match_mp_tac(thm("reduce_induct")), finish([simple])]),
  )
  let _ = lemma(
    "reduce_not_vals",
    "∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], !reduce(s, f, MAP(v_to_e, vs), s', f', es')",
    @meson.meson_tac(ths([ok, thm("all_vals_map")])),
  )
  let _ = lemma(
    "reduce_not_trap",
    "∀ s : Wstore, ∀ f : Wframe, ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], !reduce(s, f, [Trap], s', f', es')",
    @meson.meson_tac(ths([ok])),
  )
}

///|
fn prove_decompose() -> Unit raise {
  let base_rules = @bool.conjuncts_rule(thm("reduce_base_rules")).to_array()
  let reduce_rules = @bool.conjuncts_rule(thm("reduce_rules")).to_array()
  let base_reduce = lemma(
    "reduce_base_reduce",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], reduce_base(s, f, es, s', f', es') → reduce(s, f, es, s', f', es')",
    seq([
      @tactics.match_mp_tac(thm("reduce_base_induct")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List(reduce_rules.map(@tactics.match_accept_tac))),
    ]),
  )
  let lfill_nil = thm("lfill_nil")
  let base_lift = lemma(
    "reduce_base_lift",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], reduce_base(s, f, es, s', f', es') → (∃ lh : Lholed, ∃ e : List[Einstr], ∃ e' : List[Einstr], es == lfill(lh, e) && es' == lfill(lh, e') && reduce_base(s, f, e, s', f', e'))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.exists_tac(tm("(LBase(NIL, NIL) : Lholed)")),
      @simp.rewrite_tac(ths([lfill_nil])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let context = rule_of("reduce", context_rule_index)
  let decomp_reduce = lemma(
    "decomp_reduce",
    "∀ s : Wstore, ∀ f : Wframe, ∀ lh : Lholed, ∀ e : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ e' : List[Einstr], reduce_base(s, f, e, s', f', e') → reduce(s, f, lfill(lh, e), s', f', lfill(lh, e'))",
    @meson.meson_tac(ths([context, base_reduce, thm("lfilled_lfill")])),
  )
  // each rule but the context rule is a base rule; the context rule
  // composes contexts
  let base_case = seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.match_mp_tac(base_lift),
    @tactics.first(
      @list.List(
        base_rules.map(r => if @basics.is_imp(@basics.strip_forall(@kernel.concl(r)).1) {
          seq([
            @tactics.match_mp_tac(r),
            @meson.asm_meson_tac(ths([decomp_reduce])),
          ])
        } else {
          @tactics.match_accept_tac(r)
        }),
      ),
    ),
  ])
  let context_case = seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    @meson.asm_meson_tac(ths([thm("lfilled_eq"), thm("lfill_compose")])),
  ])
  let imp = lemma(
    "reduce_imp_decomp",
    "∀ s : Wstore, ∀ f : Wframe, ∀ les : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, les, s', f', les') → (∃ lh : Lholed, ∃ e : List[Einstr], ∃ e' : List[Einstr], les == lfill(lh, e) && les' == lfill(lh, e') && reduce_base(s, f, e, s', f', e'))",
    seq([
      @tactics.match_mp_tac(thm("reduce_induct")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([context_case, base_case])),
    ]),
  )
  let _ = lemma(
    "reduce_decompose",
    "∀ s : Wstore, ∀ f : Wframe, ∀ les : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, les, s', f', les') == (∃ lh : Lholed, ∃ e : List[Einstr], ∃ e' : List[Einstr], les == lfill(lh, e) && les' == lfill(lh, e') && reduce_base(s, f, e, s', f', e'))",
    @meson.meson_tac(ths([imp, decomp_reduce])),
  )
}

///|
/// Splits the assumptions that are conjunctions, disjunctions (into
/// cases) or existentials (into witnesses).
fn split_assums() -> @tactics.Tactic {
  @tactics.repeat_tac(
    @tactics.first_x_assum(th => {
      let c = @kernel.concl(th)
      if @basics.is_disj(c) || @basics.is_exists(c) || @basics.is_conj(c) {
        @tactics.strip_assume_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
  )
}

///|
/// Substitutes the assumptions `x == t` (x a variable) everywhere.
fn subst_vars() -> @tactics.Tactic {
  @tactics.repeat_tac(@tactics.first_x_assum(@tactics.subst_var_tac))
}

///|
/// Applies `lemma` (∀xs. A1 && ... && An → C) to assumptions matching its
/// premises, and adds C as an assumption (split into cases and witnesses
/// when `split`).
fn forward(lemma : @kernel.Thm, split? : Bool = true) -> @tactics.Tactic {
  @tactics.assum_list(asl => {
    let arr = asl.to_array()
    let (_, body) = @basics.strip_forall(@kernel.concl(lemma))
    let n = @basics.conjuncts(@basics.dest_imp(body).0).length()
    let rule = @drule.match_mp(lemma)
    let premises = @basics.conjuncts(@basics.dest_imp(body).0).to_array()
    // the assumptions each premise matches on its own
    let candidates = premises.map(p => arr.filter(a => (try {
      ignore(@drule.term_match(@list.List([]), p, @kernel.concl(a)))
      true
    } catch {
      _ => false
    })))
    fn attempt(chosen : Array[@kernel.Thm]) -> @kernel.Thm? {
      if chosen.length() == n {
        let mut c = chosen[n - 1]
        for i = n - 2; i >= 0; i = i - 1 {
          c = @bool.conj(chosen[i], c) catch { _ => return None }
        }
        return Some(rule(c)) catch { _ => None }
      }
      for a in candidates[chosen.length()] {
        if attempt(chosen + [a]) is Some(t) {
          return Some(t)
        }
      }
      None
    }
    guard attempt([]) is Some(th) else {
      raise Failure("forward: no assumptions match " + show_term(@kernel.concl(lemma)))
    }
    if split {
      @tactics.strip_assume_tac(th)
    } else {
      @tactics.assume_tac(th)
    }
  })
}

///|
fn list_facts() -> Array[@kernel.Thm] raise {
  let ncn = @lists.not_cons_nil()
  [@lists.cons_11(), ncn, @equal.gsym(ncn)]
}

///|
fn prove_lists() -> Unit raise {
  let append = @lists.append()
  let nil_eq_append = lemma(
    "nil_eq_append",
    "∀ x : List[A], ∀ y : List[A], NIL == APPEND(x, y) == (x == NIL && y == NIL)",
    @meson.meson_tac(ths([@lists.append_eq_nil()])),
  )
  let _ = lemma(
    "cons_eq_append",
    "∀ h : A, ∀ t : List[A], ∀ x : List[A], ∀ y : List[A], CONS(h, t) == APPEND(x, y) == ((x == NIL && y == CONS(h, t)) || (∃ x2 : List[A], x == CONS(h, x2) && t == APPEND(x2, y)))",
    seq([
      @tactics.gen_tac,
      @tactics.gen_tac,
      @lists.list_induct_tac,
      @simp.rewrite_tac(ths([append] + list_facts())),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let nil_case = seq([
    @simp.rewrite_tac(ths([append, @theorems.unwind_thm1(), nil_eq_append])),
    @tactics.try_tac(@meson.meson_tac(ths([append]))),
  ])
  let cons_case = seq([
    @tactics.gen_tac,
    @lists.list_induct_tac,
    @simp.asm_rewrite_tac(ths([append, @theorems.unwind_thm1(), nil_eq_append] + list_facts())),
    @tactics.try_tac(@meson.meson_tac(ths([]))),
  ])
  let _ = lemma(
    "append_split",
    "∀ a : List[A], ∀ b : List[A], ∀ c : List[A], ∀ d : List[A], APPEND(a, b) == APPEND(c, d) == ((∃ m : List[A], a == APPEND(c, m) && d == APPEND(m, b)) || (∃ m : List[A], c == APPEND(a, m) && b == APPEND(m, d)))",
    @tactics.thenl(@lists.list_induct_tac, @list.List([nil_case, cons_case])),
  )
}

///|
fn prove_shapes() -> Unit raise {
  let not_zero = @int.arith_rule(tm("∀ x : Num, !(0 == x + 1)"))
  let lfill_zero_trap = lemma(
    "lfill_zero_trap",
    "∀ lh : Lholed, ∀ es : List[Einstr], 0 == lh_depth(lh) && es == lfill(lh, [Trap]) → trap_top(es)",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @simp.rewrite_tac(
        ths([thm("lh_depth"), thm("lfill"), thm("trap_top"), @lists.append(), not_zero]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
    ]),
  )
  let shape_facts = [
      thm("last_redex"),
      @lists.butlast(),
      @lists.last(),
      @lists.butlast_append(),
      @lists.last_append(),
      @lists.append(),
      @lists.append_nil(),
      @lists.append_eq_nil(),
      @lists.all(),
      @lists.all_append(),
      thm("is_val_clauses"),
      thm("is_val_basic"),
      thm("all_vals_map"),
    ] +
    ctor_facts()
  let per_rule = (extra : Array[@kernel.Thm]) => seq([
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths(shape_facts)),
    @tactics.try_tac(
      @meson.asm_meson_tac(ths([lfill_zero_trap, thm("lfilled_eq")] + extra)),
    ),
  ])
  let simple_shape = lemma(
    "reduce_simple_shape",
    "∀ es : List[Einstr], ∀ es' : List[Einstr], reduce_simple(es, es') → last_redex(es) || trap_top(es)",
    seq([@tactics.match_mp_tac(thm("reduce_simple_induct")), per_rule([])]),
  )
  let _ = lemma(
    "reduce_base_shape",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], reduce_base(s, f, es, s', f', es') → last_redex(es) || trap_top(es)",
    seq([
      @tactics.match_mp_tac(thm("reduce_base_induct")),
      per_rule([@simp.rewrite_rule(ths([thm("last_redex")]))(simple_shape)]),
    ]),
  )
}

///|
fn prove_append() -> Unit raise {
  let append = @lists.append()
  let assoc_r = @equal.gsym(@lists.append_assoc())
  let all_vals_map = thm("all_vals_map")
  let all_append = @lists.all_append()
  let split = thm("append_split")
  let last_prefix = lemma(
    "last_redex_prefix",
    "∀ m : List[Einstr], ∀ m3 : List[Einstr], last_redex(APPEND(m, m3)) && !ALL(is_val, m) → m3 == NIL",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("last_redex"), @lists.butlast_append()])),
      @class.cond_cases_tac,
      @simp.asm_rewrite_tac(ths([all_append])),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let trap_prefix = lemma(
    "trap_top_prefix",
    "∀ m : List[Einstr], ∀ m3 : List[Einstr], trap_top(APPEND(m, m3)) && !ALL(is_val, m) → trap_top(m)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("trap_top")])),
      @tactics.strip_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([split, thm("cons_eq_append")]))),
      split_assums(),
      subst_vars(),
      @tactics.try_tac(
        @meson.asm_meson_tac(ths([all_vals_map, all_append, @lists.append_nil()])),
      ),
    ]),
  )
  let map_app = lemma(
    "map_app_assoc",
    "∀ vs : List[Value], ∀ vs2 : List[Value], ∀ x : List[Einstr], APPEND(MAP(v_to_e, vs), APPEND(MAP(v_to_e, vs2), x)) == APPEND(MAP(v_to_e, APPEND(vs, vs2)), x)",
    @simp.rewrite_tac(ths([@lists.map_append(), assoc_r])),
  )
  let trap_vals = lemma(
    "trap_top_vals",
    "∀ vs : List[Value], ∀ m : List[Einstr], trap_top(m) → trap_top(APPEND(MAP(v_to_e, vs), m))",
    seq([
      @simp.rewrite_tac(ths([thm("trap_top")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @meson.meson_tac(ths([map_app])),
    ]),
  )
  // splitting APPEND(es1, es2) = lfill(lh, e) at the end of es1
  let after_vals = lemma(
    "split_after_vals",
    "∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ vs : List[Value], ∀ y : List[Einstr], APPEND(es1, es2) == APPEND(MAP(v_to_e, vs), y) && !ALL(is_val, es1) → (∃ m : List[Einstr], es1 == APPEND(MAP(v_to_e, vs), m) && y == APPEND(m, es2) && !ALL(is_val, m))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([split])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([all_append, all_vals_map]))),
      @tactics.try_tac(@meson.asm_meson_tac(ths([all_vals_map, all_append]))),
    ]),
  )
  let vals_prefix = lemma(
    "map_vals_prefix",
    "∀ vs : List[Value], ∀ es1 : List[Einstr], ∀ m : List[Einstr], MAP(v_to_e, vs) == APPEND(es1, m) → ALL(is_val, es1)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(@bool.spec(@kernel.mk_var("vs", ty("List[Value]")), all_vals_map)),
      @simp.asm_rewrite_tac(ths([all_append])),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let rec_split = lemma(
    "lrec_split",
    "∀ vs : List[Value], ∀ h : Einstr, ∀ rest : List[Einstr], ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], APPEND(es1, es2) == APPEND(MAP(v_to_e, vs), CONS(h, rest)) && !ALL(is_val, es1) && !is_val(h) → (∃ x : List[Einstr], es1 == APPEND(MAP(v_to_e, vs), CONS(h, x)) && rest == APPEND(x, es2))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.strip_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([split, thm("cons_eq_append")]))),
      split_assums(),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([@lists.append_nil(), all_vals_map, all_append, @lists.all()])),
      ),
      @tactics.try_tac(@meson.asm_meson_tac(ths([vals_prefix]))),
    ]),
  )
  let last_cases = lemma(
    "last_redex_cases",
    "∀ e : List[Einstr], last_redex(e) == (∃ vs2 : List[Value], ∃ h : Einstr, e == APPEND(MAP(v_to_e, vs2), [h]) && !is_val(h))",
    seq([
      @tactics.gen_tac,
      @tactics.thenl(@tactics.eq_tac, @list.List([
      seq([
        @simp.rewrite_tac(ths([thm("last_redex")])),
        @tactics.strip_tac,
        @meson.asm_meson_tac(ths([thm("vals_map"), @lists.append_butlast_last()])),
      ]),
      seq([
        @tactics.strip_tac,
        @simp.asm_rewrite_tac(
          ths(
            [
              thm("last_redex"),
              @lists.butlast_append(),
              @lists.last_append(),
              @lists.butlast(),
              @lists.last(),
              @lists.append_eq_nil(),
              all_append,
              @lists.all(),
              all_vals_map,
              @lists.append_nil(),
            ] +
            list_facts(),
          ),
        ),
      ]),
      ])),
    ]),
  )
  let normalize = @simp.rewrite_rule(ths([assoc_r, map_app, append]))
  let base_split = lemma(
    "lbase_split",
    "∀ vs : List[Value], ∀ rest : List[Einstr], ∀ e : List[Einstr], ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], APPEND(es1, es2) == APPEND(MAP(v_to_e, vs), APPEND(e, rest)) && !ALL(is_val, es1) && (last_redex(e) || trap_top(e)) → (∃ x : List[Einstr], es1 == APPEND(MAP(v_to_e, vs), APPEND(e, x)) && rest == APPEND(x, es2)) || trap_top(es1)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("last_redex_cases"), thm("trap_top")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(normalize),
      @simp.rewrite_tac(ths([assoc_r, map_app, append])),
      @tactics.try_tac(
        @meson.asm_meson_tac(ths([rec_split, thm("is_val_clauses")])),
      ),
    ]),
  )
  let lfill = thm("lfill")
  let base_app = lemma(
    "lfill_base_app",
    "∀ vs : List[Value], ∀ x : List[Einstr], ∀ e2 : List[Einstr], ∀ es2 : List[Einstr], APPEND(lfill(LBase(vs, x), e2), es2) == APPEND(MAP(v_to_e, vs), APPEND(e2, APPEND(x, es2)))",
    @simp.rewrite_tac(ths([lfill, assoc_r])),
  )
  let rec_app = lemma(
    "lfill_rec_app",
    "∀ vs : List[Value], ∀ n : Num, ∀ e0 : List[Einstr], ∀ l : Lholed, ∀ x : List[Einstr], ∀ e2 : List[Einstr], ∀ es2 : List[Einstr], APPEND(lfill(LRec(vs, n, e0, l, x), e2), es2) == APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, lfill(l, e2)), APPEND(x, es2)))",
    @simp.rewrite_tac(ths([lfill, assoc_r, append])),
  )
  let rec_label = lemma(
    "lrec_split_label",
    "∀ vs : List[Value], ∀ n : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], ∀ rest : List[Einstr], ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ q : Bool, APPEND(es1, es2) == APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, li), rest)) && !ALL(is_val, es1) && q → (∃ x : List[Einstr], es1 == APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, li), x)) && rest == APPEND(x, es2))",
    @meson.meson_tac(ths([rec_split, thm("is_val_clauses")])),
  )
  let lfill_split = lemma(
    "lfill_split",
    "∀ lh : Lholed, ∀ e : List[Einstr], ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], APPEND(es1, es2) == lfill(lh, e) && !ALL(is_val, es1) && (last_redex(e) || trap_top(e)) → (∃ lh1 : Lholed, es1 == lfill(lh1, e) && (∀ e2 : List[Einstr], lfill(lh, e2) == APPEND(lfill(lh1, e2), es2))) || trap_top(es1)",
    seq([
      @tactics.match_mp_tac(thm("lholed_induct")),
      @tactics.thenl(@tactics.conj_tac, @list.List([
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(ths([lfill])),
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(@drule.match_mp(base_split)(th))),
        subst_vars(),
        @tactics.try_tac(@meson.asm_meson_tac(ths([lfill, base_app]))),
      ]),
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_tac,
        @simp.rewrite_tac(ths([lfill])),
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(@drule.match_mp(rec_label)(th))),
        subst_vars(),
        @tactics.try_tac(@meson.asm_meson_tac(ths([lfill, rec_app]))),
      ]),
      ])),
    ]),
  )
  let _ = lemma(
    "reduce_append",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, APPEND(es1, es2), s', f', les') && !ALL(is_val, es1) → (∃ es1' : List[Einstr], reduce(s, f, es1, s', f', es1') && les' == APPEND(es1', es2)) || trap_top(es1)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(
        @simp.rewrite_rule(ths([thm("reduce_decompose")]))(th),
      )),
      forward(thm("reduce_base_shape"), split=false),
      forward(lfill_split),
      subst_vars(),
      @tactics.try_tac(@meson.asm_meson_tac(ths([thm("decomp_reduce")]))),
    ]),
  )
}

///|
/// A step of values `cs` then an instruction `x` (not a value, Trap or a
/// label) is a base step of a suffix of `cs` then `x`.
fn prove_step_basic() -> Unit raise {
  let all_vals_map = thm("all_vals_map")
  let all_append = @lists.all_append()
  let append_nil = @lists.append_nil()
  let first_nonval = lemma(
    "snoc_first_nonval",
    "∀ vs : List[Value], ∀ cs : List[Einstr], ∀ x : Einstr, ∀ h : Einstr, ∀ rest : List[Einstr], APPEND(cs, [x]) == APPEND(MAP(v_to_e, vs), CONS(h, rest)) && ALL(is_val, cs) && !is_val(h) → h == x && rest == NIL && cs == MAP(v_to_e, vs)",
    seq([
      @lists.list_induct_tac,
      @lists.list_induct_tac,
      @simp.rewrite_tac(
        ths(
          [
            @lists.append(),
            @lists.map(),
            @lists.all(),
            thm("nil_eq_append"),
            @lists.append_eq_nil(),
            thm("is_val_clauses"),
          ] +
          list_facts(),
        ),
      ),
      @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
    ]),
  )
  let first_nonval2 = lemma(
    "snoc_first_nonval2",
    "∀ cs : List[Einstr], ∀ x : Einstr, ∀ vs : List[Value], ∀ h : Einstr, ∀ rest : List[Einstr], APPEND(cs, [x]) == APPEND(MAP(v_to_e, vs), CONS(h, rest)) && ALL(is_val, cs) → is_val(h) || (h == x && rest == NIL && cs == MAP(v_to_e, vs))",
    @meson.meson_tac(ths([first_nonval])),
  )
  let last_cases = thm("last_redex_cases")
  let assoc_r = @equal.gsym(@lists.append_assoc())
  let map_app = thm("map_app_assoc")
  let lbase = lemma(
    "step_basic_lbase",
    "∀ cs : List[Einstr], ∀ x : Einstr, ∀ vs : List[Value], ∀ rest : List[Einstr], ∀ e : List[Einstr], APPEND(cs, [x]) == APPEND(MAP(v_to_e, vs), APPEND(e, rest)) && ALL(is_val, cs) && !(x == Trap) && (last_redex(e) || trap_top(e)) → rest == NIL && (∃ suf : List[Einstr], cs == APPEND(MAP(v_to_e, vs), suf) && e == APPEND(suf, [x]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([last_cases, thm("trap_top")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([assoc_r, map_app, @lists.append()]))),
      forward(first_nonval2),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("is_val_clauses")]))),
      subst_vars(),
      @simp.asm_rewrite_tac(ths([@lists.map_append()])),
      @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
    ]),
  )
  let lrec = lemma(
    "step_basic_lrec",
    "∀ cs : List[Einstr], ∀ x : Einstr, ∀ vs : List[Value], ∀ n : Num, ∀ e0 : List[Einstr], ∀ l : Lholed, ∀ rest : List[Einstr], ∀ e : List[Einstr], APPEND(cs, [x]) == APPEND(MAP(v_to_e, vs), CONS(Label(n, e0, lfill(l, e)), rest)) && ALL(is_val, cs) && (∀ n2 : Num, ∀ e2 : List[Einstr], ∀ li : List[Einstr], !(x == Label(n2, e2, li))) → false",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      forward(first_nonval2),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("is_val_clauses")]))),
      @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
    ]),
  )
  let lfill = thm("lfill")
  let lh = @kernel.mk_var("lh", ty("Lholed"))
  let _ = lemma(
    "step_basic",
    "∀ s : Wstore, ∀ f : Wframe, ∀ cs : List[Einstr], ∀ x : Einstr, ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, APPEND(cs, [x]), s', f', les') && ALL(is_val, cs) && !(x == Trap) && (∀ n : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], !(x == Label(n, e0, li))) → (∃ pre : List[Einstr], ∃ suf : List[Einstr], ∃ e' : List[Einstr], cs == APPEND(pre, suf) && les' == APPEND(pre, e') && reduce_base(s, f, APPEND(suf, [x]), s', f', e'))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(
        @simp.rewrite_rule(ths([thm("reduce_decompose")]))(th),
      )),
      @tactics.disj_cases_tac(@bool.spec(lh, @ind_types.cases("lholed"))),
      split_assums(),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([lfill]))),
      forward(thm("reduce_base_shape"), split=false),
      @tactics.try_tac(forward(lrec)),
      @tactics.try_tac(forward(lbase)),
      subst_vars(),
      @simp.rewrite_tac(ths([lfill, append_nil])),
      @tactics.try_tac(@meson.asm_meson_tac(ths([append_nil]))),
    ]),
  )
}

///|
/// Lemmas the inversion procedure rewrites with.
fn prove_inversion_lemmas() -> Unit raise {
  let _ = lemma(
    "map_v_to_e_eq_cons",
    "∀ vs : List[Value], ∀ h : Einstr, ∀ t : List[Einstr], MAP(v_to_e, vs) == CONS(h, t) == (∃ v : Value, ∃ vs2 : List[Value], vs == CONS(v, vs2) && h == v_to_e(v) && t == MAP(v_to_e, vs2))",
    @meson.meson_tac(ths([thm("map_v_to_e_cons")])),
  )
  let _ = lemma(
    "eq_v_to_e",
    "∀ e : Einstr, ∀ v : Value, e == v_to_e(v) == ((∃ x : V_num, v == V_num(x) && e == Basic(EConstNum(x))) || (∃ y : V_vec, v == V_vec(y) && e == Basic(EConstVec(y))) || (∃ r : V_ref, v == V_ref(r) && e == Ref(r)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disj_cases_tac(
        @bool.spec(@kernel.mk_var("v", ty("Value")), @ind_types.cases("value")),
      ),
      split_assums(),
      subst_vars(),
      @simp.rewrite_tac(ths([thm("v_to_e")] + ctor_facts())),
      @tactics.try_tac(@meson.meson_tac(ths([]))),
    ]),
  )
  let _ = lemma(
    "lfilled_trap_iff",
    "∀ es : List[Einstr], (∃ lh : Lholed, Lfilled(0, lh, [Trap], es)) == trap_top(es)",
    seq([
      @tactics.gen_tac,
      @tactics.thenl(
        @tactics.eq_tac,
        @list.List([
          seq([
            @simp.rewrite_tac(ths([thm("lfilled_eq")])),
            @tactics.repeat_tac(@tactics.strip_tac),
            forward(thm("lfill_zero_trap")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            @simp.rewrite_tac(ths([thm("trap_top")])),
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.exists_tac(tm("LBase((vs : List[Value]), (r : List[Einstr]))")),
            @simp.asm_rewrite_tac(
              ths([thm("lfilled_eq"), thm("lfill"), thm("lh_depth"), @lists.append()]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}

///|
let inversion_rewrite : Ref[@equal.Conv?] = Ref::{ val: None }

///|
/// Simplifies what a step can be: case theorems, list and constructor
/// equations, miniscoping and unwinding of existentials, until nothing
/// changes.
fn inversion_conv(t : @kernel.Term) -> @kernel.Thm raise {
  let rw = match inversion_rewrite.val {
    Some(c) => c
    None => {
      let logic = [
        @theorems.exists_or_thm(),
        @theorems.left_exists_and_thm(),
        @theorems.right_exists_and_thm(),
        @class.taut(tm("(p && (q || r)) == ((p && q) || (p && r))")),
        @class.taut(tm("((q || r) && p) == ((q && p) || (r && p))")),
      ]
      let lists = [
        @lists.append(),
        @lists.append_nil(),
        @lists.append_eq_nil(),
        @lists.map_eq_nil(),
        thm("nil_eq_append"),
        thm("cons_eq_append"),
        thm("map_v_to_e_eq_cons"),
        thm("eq_v_to_e"),
        thm("v_to_e"),
        thm("lfilled_trap_iff"),
        thm("trap_top"),
        thm("reduce_base_cases"),
        thm("reduce_simple_cases"),
      ]
      // constructors the rules compare, beyond ctor_facts
      let more = []
      for t in [
        "cvtop", "t_num", "t_vec", "t_ref", "valtype", "sx", "sat", "v_num", "v_vec",
        "v_ref", "tb", "tf", "tg", "wframe", "inst", "limit_t", "unop", "unop_i", "binop",
        "binop_i", "relop", "relop_i", "testop", "tp_num",
      ] {
        // a type with one constructor has no distinctness theorem, and one
        // whose constructors take no arguments no injectivity theorem
        let d = try Some(@ind_types.distinctness(t)) catch { _ => None }
        if d is Some(d) {
          more.push(d)
          more.push(@equal.gsym(d))
        }
        more.push(@ind_types.injectivity(t)) catch { _ => () }
      }
      let c = @simp.rewrite_conv(ths(logic + lists + list_facts() + ctor_facts() + more))
      inversion_rewrite.val = Some(c)
      c
    }
  }
  let once = @equal.thenc(
    rw,
    @equal.top_depth_conv(@ind_types.unwind_conv),
  )
  let mut th = @kernel.refl(t)
  for _ in 0..<40 {
    let cur = @equal.rhs(@kernel.concl(th))
    let next = once(cur)
    if @basics.aconv(@equal.rhs(@kernel.concl(next)), cur) {
      return th
    }
    th = @kernel.trans(th, next)
  }
  raise Failure("wasmcert/wasm step_cases: the simplification does not settle")
}

///|
/// What the instructions `es` (values, then one basic instruction) can
/// step to in store `s` and frame `f`:
/// ⊢ ∀ s' f' es'. reduce(s, f, es, s', f', es') → D, D the possible
/// results with their side conditions, computed as far as they go (for
/// concrete operands, the one result).
pub fn step_cases(
  s : @kernel.Term,
  f : @kernel.Term,
  es : @kernel.Term,
) -> @kernel.Thm raise {
  props()
  let items = @basics.dest_list(es).to_array()
  guard items.last() is Some(x) && head_args(x).0 == "Basic" else {
    raise Failure("wasmcert/wasm step_cases: the list does not end in a basic instruction")
  }
  let cs = items[:items.length() - 1]
  for c in cs {
    if as_value(c) is None {
      raise Failure("wasmcert/wasm step_cases: " + show_term(c) + " is not a value")
    }
  }
  let s2 = @kernel.mk_var("s'", hol_type("wstore"))
  let f2 = @kernel.mk_var("f'", hol_type("wframe"))
  let es2 = @kernel.mk_var("es'", @kernel.type_of(es))
  let th = @bool.ispecl(
    @list.List([s, f, einstr_list(cs), x, s2, f2, es2]),
    thm("step_basic"),
  )
  // the side conditions hold and APPEND(cs, [x]) is es
  let side = @simp.rewrite_rule(
    ths([@lists.append(), @lists.all(), thm("is_val_clauses"), thm("is_val_basic")] + ctor_facts()),
  )
  let th = side(th)
  let (ant, _) = @basics.dest_imp(@kernel.concl(th))
  let want = call("reduce", [s, f, es, s2, f2, es2])
  if !@basics.aconv(ant, want) {
    raise Failure("wasmcert/wasm step_cases: side conditions left: " + show_term(ant))
  }
  let th = @equal.conv_rule(@equal.rand_conv(inversion_conv), th)
  // compute the side conditions (the evaluator's definitions and
  // arithmetic), and simplify again, until nothing changes
  setup()
  let compute = (t : @kernel.Term) => {
    let mut acc = @kernel.refl(t)
    for _ in 0..<6 {
      let cur = @equal.rhs(@kernel.concl(acc))
      let a = eval_conv(cur)
      let next = @kernel.trans(a, inversion_conv(@equal.rhs(@kernel.concl(a))))
      if @basics.aconv(@equal.rhs(@kernel.concl(next)), cur) {
        break
      }
      acc = @kernel.trans(acc, next)
    }
    acc
  }
  let th = @equal.conv_rule(@equal.rand_conv(compute), th)
  @bool.gen(s2, @bool.gen(f2, @bool.gen(es2, th)))
}
