// Symbolic execution: a tactic that proves sl_triple goals on exact states
// by running the code.
//
// `sym_tac` works on goals sl_triple_l(st(v, l, R), code, q, ls). It takes
// the first instruction and:
//
// - for straight-line instructions, instantiates the st_ rule whose
//   precondition matches the state (st_const, st_binop, ..., st_arr_load),
//   computes the result (app_binop and the others, written out by `norm`),
//   and continues from the rule's postcondition (sl_step_l);
// - for br_if, continues with c = 0, and leaves br's goal with c ≠ 0
//   (sl_br_if_st);
// - for if, block and loop, goes into the branches and bodies (sl_if_st,
//   sl_block_st, sl_loop_st), taking the loop's invariant from the caller,
//   and, if more code follows, the state after it (sl_cons_l);
// - for br and the end of the code, leaves an entailment (sl_br_st,
//   sl_nil_st).
//
// A precondition that is not an exact state (a loop invariant) is first
// written as ∃ xs. facts && st(v, l, R): the xs become variables and the
// facts assumptions (sl_ex_l, sl_pure_l). What is left are the
// verification conditions: entailments ∀ gs ms h. R(gs, ms, h) → ...,
// written out and simplified (`vc_tac`), and side conditions of rules
// (an array element's address). `sym_prove` proves a triple with them.

///|
pub let sa_false : String = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => false"

///|
/// The name of a rule for g triples (specs.mbt): sl_x_l is sl_x_g, and
/// any other sl_x is sl_x_g.
fn g_name(name : String) -> String {
  if name.has_suffix("_l") {
    name.unsafe_substring(start=0, end=name.length() - 2) + "_g"
  } else {
    name + "_g"
  }
}

///|
fn prove_sym_rules() -> Unit raise {
  prove_sym_derived(false)
  let _ = lemma(
    "wasm_bool_zero",
    "∀ b : Bool, (wasm_bool(b) == word(0)) == !b",
    seq([
      @tactics.gen_tac,
      @class.bool_cases_tac(tm("(b : Bool)")),
      @simp.rewrite_tac(
        ths([@wasm.thm("wasm_bool"), @equal.gsym(@words.val_eq()), @words.val_word_1(), @words.val_word_0(), arith("!(1 == 0)")]),
      ),
    ]),
  )
}

///|
/// The rules sym_tac uses, from the triple's basic rules: for sl_triple_l
/// (g = false), or for g triples (specs.mbt), where each also takes G, fs,
/// tabs, inst and rp first, and is named by g_name.
fn prove_sym_derived(g : Bool) -> Unit raise {
  let sa = sassn
  let st = thm("st")
  // the triple, the quantifiers for G, fs, tabs, inst and rp, and the names
  let tr = (p : String, bs : String, q : String, ls : String) => if g {
    triple_g(p, bs, q, ls)
  } else {
    "sl_triple_l(\{p}, \{bs}, \{q}, \{ls})"
  }
  let env = if g { env_vars() } else { "" }
  let name = (n : String) => if g { g_name(n) } else { n }
  let rule = (n : String) => thm(name(n))
  let env_terms = if g {
    ["(G : \{specs_ty})", "(fs : List[Cl])", "(tabs : List[(Tab_t, List[V_ref])])", "(inst : Inst)", "(rp : \{sa})"].map(tm)
  } else {
    []
  }
  let spec_rule = (n : String, args : Array[String]) => @bool.ispecl(@list.List(env_terms + args.map(tm)), rule(n))
  // reasoning about pre- and postconditions that are lambdas
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([st])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let conseq = (p : String, q : String, ls : String, triple : @tactics.Tactic) => seq([
    @tactics.match_mp_tac(rule("sl_conseq_l")),
    @tactics.exists_tac(tm(p)),
    @tactics.exists_tac(tm(q)),
    @tactics.exists_tac(tm(ls)),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([solve(triple), solve(simple)])),
  ])
  let _ = lemma(
    name("sl_pre_l"),
    "\{env}∀ p : \{sa}, ∀ p2 : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, p2(vs, lc, gs, ms, h) → p(vs, lc, gs, ms, h)) && \{tr("p", "bs", "q", "ls")} → \{tr("p2", "bs", "q", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      conseq("(p : \{sa})", "(q : \{sa})", "(ls : List[\{sa}])", @meson.asm_meson_tac(ths([]))),
    ]),
  )
  // [i] then rest
  let cons_append = (i : String, rest : String) => @equal.gsym(
    @simp.rewrite_conv(ths([@lists.append()]))(tm("APPEND([\{i}], \{rest})")),
  )
  if !g {
    let _ = lemma(
      "sl_step_l",
      "∀ p : \{sa}, ∀ i : B_e, ∀ q : \{sa}, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], sl_triple(p, [i], q) → sl_triple_l(q, rest, r, ls) → sl_triple_l(p, CONS(i, rest), r, ls)",
      seq([
        @tactics.repeat_tac(@tactics.strip_tac),
        @tactics.subst1_tac(cons_append("(i : B_e)", "(rest : List[B_e])")),
        @tactics.match_mp_tac(thm("sl_seq_l")),
        @tactics.exists_tac(tm("(q : \{sa})")),
        @meson.asm_meson_tac(ths([thm("sl_triple_l_of")])),
      ]),
    )
  }
  let _ = lemma(
    name("sl_cons_l"),
    "\{env}∀ q : \{sa}, ∀ p : \{sa}, ∀ i : B_e, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], \{tr("p", "[i]", "q", "ls")} && \{tr("q", "rest", "r", "ls")} → \{tr("p", "CONS(i, rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.subst1_tac(cons_append("(i : B_e)", "(rest : List[B_e])")),
      @tactics.match_mp_tac(rule("sl_seq_l")),
      @tactics.exists_tac(tm("(q : \{sa})")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let state = "st((v : List[Value]), (l : List[Value]), (R : \{rty}))"
  let vars = "\{env}∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}"
  let ls = "(ls : List[\{sa}])"
  let _ = lemma(
    name("sl_nil_st"),
    "\{vars}, ∀ r : \{sa}, ∀ ls : List[\{sa}], (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → r(v, l, gs, ms, h)) → \{tr(state, "NIL", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      conseq(state, state, ls, @tactics.match_accept_tac(rule("sl_nil_l"))),
    ]),
  )
  let br_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && EL(i, ls, vb, lc, gs, ms, h))"
  let _ = lemma(
    name("sl_br_st"),
    "\{vars}, ∀ i : Num, ∀ r : \{sa}, ∀ ls : List[\{sa}], i < LENGTH(ls) && (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → (∃ vs0 : List[Value], ∃ vb : List[Value], v == APPEND(vs0, vb) && EL(i, ls, vb, l, gs, ms, h))) → \{tr(state, "[Br(i)]", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      conseq(
        br_pre,
        sa_false,
        ls,
        seq([@tactics.match_mp_tac(rule("sl_br")), @tactics.first_assum(th => @tactics.accept_tac(th))]),
      ),
    ]),
  )
  // the precondition of sl_br_if and sl_if, for p = st(v, l, R)
  let x = "V_num(ConstInt32((c : \{w32})))"
  let pre_c = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [\{x}]) && \{state}(vs0, lc, gs, ms, h))"
  let top = "st(APPEND(v, [\{x}]), l, R)"
  let to_pre_c = (rest : @tactics.Tactic) => seq([
    @tactics.match_mp_tac(rule("sl_pre_l")),
    @tactics.exists_tac(tm(pre_c)),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([solve(@simp.rewrite_tac(ths([thm("st_snoc_ex")]))), rest]),
    ),
  ])
  let _ = lemma(
    name("sl_br_if_st"),
    "\{vars}, ∀ c : \{w32}, ∀ i : Num, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (!(c == word(0)) → \{tr(state, "[Br(i)]", sa_false, "ls")}) && (c == word(0) → \{tr(state, "rest", "r", "ls")}) → \{tr(top, "CONS(Br_if(i), rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.subst1_tac(cons_append("Br_if((i : Num))", "(rest : List[B_e])")),
      @tactics.match_mp_tac(rule("sl_seq_l")),
      @tactics.exists_tac(
        tm("(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (c : \{w32}) == word(0) && \{state}(vs, lc, gs, ms, h)"),
      ),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          to_pre_c(
            @tactics.thenl(
              seq([@tactics.match_mp_tac(rule("sl_br_if")), @tactics.conj_tac]),
              @list.List([
                // c ≠ 0: br, whose postcondition is false
                seq([@tactics.disch_tac, conseq(state, sa_false, ls, @meson.asm_meson_tac(ths([])))]),
                seq([@tactics.disch_tac, @tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))]),
              ]),
            ),
          ),
          seq([
            @tactics.match_mp_tac(rule("sl_pure_l")),
            @simp.rewrite_tac(ths([@class.eta_ax()])),
            @tactics.first_assum(th => @tactics.accept_tac(th)),
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    name("sl_if_st"),
    "\{vars}, ∀ c : \{w32}, ∀ tb : Tb, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (!(c == word(0)) → \{tr(state, "[Block(tb, bs1)]", "r", "ls")}) && (c == word(0) → \{tr(state, "[Block(tb, bs2)]", "r", "ls")}) → \{tr(top, "[If(tb, bs1, bs2)]", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      to_pre_c(
        seq([
          @tactics.match_mp_tac(rule("sl_if")),
          @simp.rewrite_tac(ths([@class.eta_ax()])),
          @tactics.first_assum(th => @tactics.accept_tac(th)),
        ]),
      ),
    ]),
  )
  // the body's postcondition and label: what r says after vs
  let after = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (r : \{sa})(APPEND(v, vs), lc, gs, ms, h)"
  let ot = "(ot : Option[Valtype])"
  let lb = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(vs) == LENGTH(tbv_results(\{ot})) && (r : \{sa})(APPEND(v, vs), lc, gs, ms, h)"
  let block = @equal.beta_rule(
    spec_rule("sl_block", [ot, "(bs : List[B_e])", "st((NIL : List[Value]), l, R)", after, lb, ls, "(v : List[Value])"]),
  )
  let (_, block_concl) = @basics.dest_imp(@kernel.concl(block))
  let (block_pre, _, block_post, _) = triple_l_terms(block_concl)
  let _ = lemma(
    name("sl_block_st"),
    "\{vars}, ∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], \{tr("st(NIL, l, R)", "bs", after, "CONS(\{lb}, ls)")} → \{tr(state, "[Block(Tbv(ot), bs)]", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(rule("sl_conseq_l")),
      @tactics.exists_tac(block_pre),
      @tactics.exists_tac(block_post),
      @tactics.exists_tac(tm(ls)),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([
        solve(seq([
          @tactics.match_mp_tac(block),
          @tactics.conj_tac,
          seq([@tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))]),
          @tactics.first_assum(th => @tactics.accept_tac(th)),
        ])),
        solve(simple),
      ])),
    ]),
  )
  let linv = "(linv : (List[Value], List[Value], Num, \{heap}) -> Bool)"
  let lbl = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && \{linv}(lc, gs, ms, h)"
  let looped = @equal.beta_rule(spec_rule("sl_loop", [ot, "(bs : List[B_e])", linv, after, ls, "(v : List[Value])"]))
  let (_, loop_concl) = @basics.dest_imp(@kernel.concl(looped))
  let (loop_pre, _, loop_post, _) = triple_l_terms(loop_concl)
  let _ = lemma(
    name("sl_loop_st"),
    "\{env}∀ linv : (List[Value], List[Value], Num, \{heap}) -> Bool, ∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → linv(l, gs, ms, h)) && \{tr(lbl, "bs", after, "CONS(\{lbl}, ls)")} → \{tr(state, "[Loop(Tbv(ot), bs)]", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(rule("sl_conseq_l")),
      @tactics.exists_tac(loop_pre),
      @tactics.exists_tac(loop_post),
      @tactics.exists_tac(tm(ls)),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([
        solve(seq([@tactics.match_mp_tac(looped), @tactics.first_assum(th => @tactics.accept_tac(th))])),
        solve(simple),
      ])),
    ]),
  )
}

// ---------------------------------------------------------------------------
// The tactic.
// ---------------------------------------------------------------------------

///|
/// What `sym_tac` needs besides the goal: the loops' invariants (each
/// Loop instruction with its linv) and rewrites for the verification
/// conditions.
priv struct Sym {
  loops : Array[(@kernel.Term, @kernel.Term)]
  afters : Array[(@kernel.Term, @kernel.Term)]
  rules : Array[String]
  rws : Array[@kernel.Thm]
  // for g triples: theorems ∀ xs. G(a, P, Q), the specs calls use
  specs : Array[@kernel.Thm]
  // for each call, in order, if given: a spec (its index in specs) and
  // the terms for its ∀s; the call then leaves P of the arguments to prove
  calls : Array[(Int, Array[String])]
  next_call : Ref[Int]
}

///|
/// Whether the goal is a g triple (specs.mbt).
fn is_g(goal : @kernel.Term) -> Bool {
  head_name(goal) == "sl_triple_g"
}

///|
/// The rule `name` for the goal's triple: as it is for sl_triple_l, and
/// g_name(name) with the goal's G, fs, tabs, inst and rp for a g triple.
fn rule_of(goal : @kernel.Term, name : String) -> @kernel.Thm raise {
  if is_g(goal) {
    let args = @basics.strip_comb(goal).1.to_array()
    @bool.ispecl(@list.List(args[0:5].to_owned()), thm(g_name(name)))
  } else {
    thm(name)
  }
}

///|
/// Rewrites `norm_thms` (and `extra`) and numeral arithmetic to the end.
fn norm_conv(extra? : Array[@kernel.Thm] = []) -> @equal.Conv raise {
  let rw = @simp.rewrite_conv(ths(norm_thms() + extra))
  @equal.repeatc(@equal.changed_conv(@equal.thenc(rw, @calc_num.num_reduce_conv)))
}

///|
/// A conversion at the precondition of sl_triple_l(p, bs, q, ls).
fn pre_conv(c : @equal.Conv) -> @equal.Conv {
  @equal.rator_conv(@equal.rator_conv(@equal.rator_conv(@equal.rand_conv(c))))
}

///|
/// A conversion at the stack of st(v, l, R).
fn stack_conv(c : @equal.Conv) -> @equal.Conv {
  @equal.rator_conv(@equal.rator_conv(@equal.rand_conv(c)))
}

///|
let value_ty : Ref[@kernel.HolType?] = Ref::{ val: None }

///|
fn values_ty() -> @kernel.HolType raise {
  match value_ty.val {
    Some(t) => t
    None => {
      let t = @kernel.type_of(tm("(x : Value)"))
      value_ty.val = Some(t)
      t
    }
  }
}

///|
fn mk_append(a : @kernel.Term, b : @kernel.Term) -> @kernel.Term raise {
  let va = tm("(a : List[Value])")
  let vb = tm("(b : List[Value])")
  @kernel.vsubst(@list.List([(a, va), (b, vb)]), tm("APPEND((a : List[Value]), (b : List[Value]))"))
}

///|
/// The stack s as (prefix, its top k values): s is `[x1, ..., xn]`,
/// `APPEND(vs0, [x1, ..., xn])` or `vs0`.
fn split_stack(s : @kernel.Term, k : Int) -> (@kernel.Term, Array[@kernel.Term]) raise {
  let (base, elems) : (@kernel.Term?, Array[@kernel.Term]) = match args_of(s, "APPEND", 2) {
    Some([b, l]) if @basics.is_list(l) => (Some(b), @basics.dest_list(l).to_array())
    _ => if @basics.is_list(s) { (None, @basics.dest_list(s).to_array()) } else { (Some(s), []) }
  }
  let n = elems.length()
  if k > n {
    raise Failure("certimoon/logic: sym: the stack " + show(s) + " has fewer than " + k.to_string() + " values on top")
  }
  let below = @lists.mk_list(@list.List(elems[0:n - k].to_owned()), values_ty())
  let prefix = match base {
    None => below
    Some(b) => if n == k { b } else { mk_append(b, below) }
  }
  (prefix, elems[n - k:].to_owned())
}

///|
/// Rewrites the precondition's stack, `APPEND(prefix, [x1, ..., xk])`
/// (after split_tac), to `APPEND(prefix, APPEND([x1, ..., xk-1], [xk]))`.
fn last_apart_tac() -> @tactics.Tactic {
  g => {
    let (p, _, _, _) = triple_l_terms(g.1)
    guard args_of(p, "st", 3) is Some([s, _, _]) && args_of(s, "APPEND", 2) is Some([_, top]) else {
      raise Failure("last_apart_tac")
    }
    let items = @basics.dest_list(top).to_array()
    let n = items.length()
    let apart = mk_append(
      @lists.mk_list(@list.List(items[:n - 1].to_owned()), values_ty()),
      @lists.mk_list(@list.List([items[n - 1]]), values_ty()),
    )
    let th = @simp.rewrite_conv(ths([@lists.append()]))(apart)
    if !@basics.aconv(@equal.rhs(@kernel.concl(th)), top) {
      raise Failure("certimoon/logic: sym: cannot take the top apart in " + show(s))
    }
    let back = @equal.sym(th)
    let at_top : @equal.Conv = t => if @basics.aconv(t, top) { back } else { raise Failure("last_apart_tac") }
    @tactics.conv_tac(pre_conv(stack_conv(@equal.rand_conv(at_top))))(g)
  }
}

///|
/// Rewrites the precondition's stack to `APPEND(prefix, [top k])`.
fn split_tac(k : Int) -> @tactics.Tactic {
  g => {
    let (p, _, _, _) = triple_l_terms(g.1)
    guard args_of(p, "st", 3) is Some([s, _, _]) else { raise Failure("split_tac") }
    let (prefix, top) = split_stack(s, k)
    let split = mk_append(prefix, @lists.mk_list(@list.List(top), values_ty()))
    let th = norm_conv()(split)
    if !@basics.aconv(@equal.rhs(@kernel.concl(th)), s) {
      raise Failure("certimoon/logic: sym: cannot split the stack " + show(s))
    }
    let back = @equal.sym(th)
    let at_s : @equal.Conv = t => if @basics.aconv(t, s) { back } else { raise Failure("split_tac") }
    @tactics.conv_tac(pre_conv(stack_conv(at_s)))(g)
  }
}

///|
/// `th` (∀ xs. ...) specialised to variables not in `avoid`.
fn fresh_spec(th : @kernel.Thm, avoid : @list.List[@kernel.Term]) -> @kernel.Thm raise {
  let (vs, _) = @basics.strip_forall(@kernel.concl(th))
  @bool.ispecl(@basics.variants(avoid, vs), th)
}

///|
/// The st_ rules sym_tac runs straight-line code with.
pub let step_rules : Array[String] = [
  "st_const", "st_binop", "st_testop", "st_relop", "st_local_get", "st_local_set",
  "st_arr_store", "st_arr_load", "st_arr_load_at", "st_arr_store_at",
]

///|
/// The rule for `instr` from the state st(s, l, r): sl_triple(st(s, l, r),
/// [instr], post), written out, after a side condition if it keeps one.
fn step_rule(rules : Array[String], instr : @kernel.Term, p : @kernel.Term) -> @kernel.Thm raise {
  guard args_of(p, "st", 3) is Some([s, l, r]) else { raise Failure("step_rule") }
  let avoid = @kernel.frees(p) + @kernel.frees(instr)
  for name in rules {
    let th = @simp.rewrite_rule(ths([@class.eta_ax()]))(fresh_spec(thm(name), avoid))
    let c = @kernel.concl(th)
    let triple = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
    guard args_of(triple, "sl_triple", 3) is Some([ppat, code, _]) else { continue }
    let ipat = @basics.dest_list(code).head().unwrap()
    if head_name(ipat) != head_name(instr) {
      continue
    }
    guard args_of(ppat, "st", 3) is Some([spat, _, _]) else { continue }
    let k = match args_of(spat, "APPEND", 2) {
      Some([_, top]) => @basics.dest_list(top).length()
      _ => 0
    }
    guard (try Some(split_stack(s, k)) catch { _ => None }) is Some((prefix, top)) else { continue }
    let split = if k == 0 { s } else { mk_append(prefix, @lists.mk_list(@list.List(top), values_ty())) }
    let (st_c, _) = @basics.strip_comb(ppat)
    let target_p = @basics.list_mk_comb(st_c, @list.List([split, l, r]))
    let pat = @kernel.rator(triple)
    let sl_triple_c = @kernel.rator(@kernel.rator(pat))
    let target = @kernel.mk_comb(
      @kernel.mk_comb(sl_triple_c, target_p),
      @lists.mk_list(@list.List([instr]), @kernel.type_of(instr)),
    )
    guard (try Some(@drule.term_match(@list.List([]), pat, target)) catch { _ => None }) is Some(i) else { continue }
    let th = @drule.instantiate_rule(i, th)
    return norm(compute_results(th))
  }
  raise Failure("certimoon/logic: sym: no rule for " + show(instr) + " from " + show(p))
}

///|
/// For a rule whose hypothesis is `x == SOME(c)` (c a variable): c is the
/// value x computes to.
fn compute_results(th : @kernel.Thm) -> @kernel.Thm raise {
  let c = @kernel.concl(th)
  if !@basics.is_imp(c) {
    return th
  }
  let (h, _) = @basics.dest_imp(c)
  guard h is Comb(Comb(Const("=", _), x), Comb(Const("SOME", _), Var(_, _) as v)) else { return th }
  let computed = @equal.rhs(@kernel.concl(norm_conv()(x)))
  guard computed is Comb(Const("SOME", _), d) else {
    raise Failure("certimoon/logic: sym: " + show(x) + " is " + show(computed) + ", not SOME of a value")
  }
  @bool.spec(d, @bool.gen(v, th))
}

///|
/// The facts a branch adds, simplified.
fn fact_tac() -> @tactics.Tactic {
  @tactics.disch_then(th => {
    let th = @simp.rewrite_rule(ths([thm("wasm_bool_zero")]))(th)
    @tactics.strip_assume_tac(th)
  })
}

///|
/// Simplifies a verification condition: the state written out, the
/// precondition's R assumed, lists and values compared elementwise, ∃s
/// with an equation solved; then tries to finish with the assumptions.
fn vc_tac(sym : Sym) -> @tactics.Tactic raise {
  let rws = [
    thm("st"),
    thm("tbv_results"),
    @lists.length_eq_nil(),
    @lists.cons_11(),
    @ind_types.injectivity("value"),
    @ind_types.injectivity("v_num"),
  ] + sym.rws
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.conv_tac(norm_conv(extra=rws)),
    @tactics.try_tac(@tactics.disch_then(th => @tactics.strip_assume_tac(th))),
    @tactics.try_tac(@tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv))),
    @simp.asm_rewrite_tac(ths(norm_thms() + rws)),
    @tactics.try_tac(@tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv))),
    @simp.asm_rewrite_tac(ths(norm_thms() + rws)),
  ])
}

///|
/// Runs the goal's code (see the file comment).
fn sym_tac(sym : Sym) -> @tactics.Tactic {
  g => {
    let (p, code, _, _) = triple_l_terms(g.1)
    // the precondition, written out as the next step will see it
    let p = @equal.rhs(@kernel.concl(norm_conv()(p)))
    let renorm = @tactics.conv_tac(pre_conv(norm_conv()))
    if args_of(p, "st", 3) is None {
      return @tactics.then_tac(intro_tac(), sym_tac(sym))(g)
    }
    if @basics.is_list(code) && @basics.dest_list(code).is_empty() {
      return seq([renorm, @tactics.match_mp_tac(rule_of(g.1, "sl_nil_st")), vc_tac(sym)])(g)
    }
    guard args_of(code, "CONS", 2) is Some([instr, rest]) else {
      raise Failure("certimoon/logic: sym: the code is not a list: " + show(code))
    }
    let last = @basics.is_list(rest) && @basics.dest_list(rest).is_empty()
    let need_last = (what : String) => if !last {
      raise Failure("certimoon/logic: sym: " + what + " must end its instruction list")
    }
    let name = head_name(instr)
    if !last && (name == "Block" || name == "If" || name == "Loop") {
      // [instr] to the state the caller gives, then the rest from it
      let mut after = None
      for a in sym.afters {
        if @basics.aconv(a.0, instr) {
          after = Some(a.1)
        }
      }
      guard after is Some(q) else {
        raise Failure("certimoon/logic: sym: no state given for after " + show(instr))
      }
      return seq([
        renorm,
        @tactics.match_mp_tac(@bool.ispec(q, rule_of(g.1, "sl_cons_l"))),
        @tactics.conj_tac,
        sym_tac(sym),
      ])(g)
    }
    match name {
      "Br" => {
        need_last("br")
        seq([renorm, @tactics.match_mp_tac(rule_of(g.1, "sl_br_st")), @tactics.conj_tac, vc_tac(sym)])(g)
      }
      "Br_if" =>
        seq([
          renorm,
          split_tac(1),
          @tactics.match_mp_tac(rule_of(g.1, "sl_br_if_st")),
          @tactics.conj_tac,
          fact_tac(),
          sym_tac(sym),
        ])(g)
      "If" => {
        need_last("if")
        seq([
          renorm,
          split_tac(1),
          @tactics.match_mp_tac(rule_of(g.1, "sl_if_st")),
          @tactics.conj_tac,
          fact_tac(),
          sym_tac(sym),
        ])(g)
      }
      "Block" => {
        need_last("block")
        seq([renorm, @tactics.match_mp_tac(rule_of(g.1, "sl_block_st")), beta_goal(), sym_tac(sym)])(g)
      }
      "Loop" => {
        need_last("loop")
        let mut inv = None
        for l in sym.loops {
          if @basics.aconv(l.0, instr) {
            inv = Some(l.1)
          }
        }
        guard inv is Some(inv) else {
          raise Failure("certimoon/logic: sym: no invariant for " + show(instr))
        }
        @tactics.thenl(
          seq([renorm, @tactics.match_mp_tac(@bool.ispec(inv, rule_of(g.1, "sl_loop_st"))), beta_goal(), @tactics.conj_tac]),
          @list.List([vc_tac(sym), sym_tac(sym)]),
        )(g)
      }
      "Return" if is_g(g.1) => seq([renorm, @tactics.match_mp_tac(rule_of(g.1, "sl_return_st")), vc_tac(sym)])(g)
      "Call" if is_g(g.1) && sym.next_call.val < sym.calls.length() => {
        let (which, terms) = sym.calls[sym.next_call.val]
        sym.next_call.val = sym.next_call.val + 1
        let spec = @bool.ispecl(@list.List(terms.map(tm)), sym.specs[which])
        let k = spec_arity(spec)
        let rule = @drule.match_mp(rule_of(g.1, "sl_call_spec"))(spec)
        @tactics.thenl(
          seq([renorm, split_tac(k), @tactics.match_mp_tac(rule), @tactics.conj_tac]),
          @list.List([seq([beta_goal(), vc_tac(sym)]), seq([beta_goal(), sym_tac(sym)])]),
        )(g)
      }
      "Call_indirect" if is_g(g.1) => {
        // the index c on top, and below it the arguments of a spec's P
        guard args_of(p, "st", 3) is Some([s, l, r]) else { raise Failure("certimoon/logic: sym: call_indirect") }
        let below = @basics.list_mk_icomb("st", @list.List([split_stack(s, 1).0, l, r]))
        let (k, spec) = call_spec(sym, g.1, instr, below, rule_name="sl_call_indirect_st")
        let rule = @drule.match_mp(rule_of(g.1, "sl_call_indirect_st"))(spec)
        @tactics.thenl(
          seq([renorm, split_tac(k + 1), last_apart_tac(), @tactics.match_mp_tac(rule), @tactics.conj_tac]),
          @list.List([vc_tac(sym), sym_tac(sym)]),
        )(g)
      }
      "Call" if is_g(g.1) => {
        let (k, spec) = call_spec(sym, g.1, instr, p)
        let rule = @drule.match_mp(rule_of(g.1, "sl_call_st"))(spec)
        @tactics.thenl(
          seq([renorm, split_tac(k), @tactics.match_mp_tac(rule), @tactics.conj_tac]),
          @list.List([vc_tac(sym), sym_tac(sym)]),
        )(g)
      }
      _ => {
        let th = step_rule(sym.rules, instr, p)
        let c = @kernel.concl(th)
        if @basics.is_imp(c) {
          let (h, _) = @basics.dest_imp(c)
          @tactics.thenl(
            seq([renorm, @tactics.subgoal_then(h, hth => step_tac(@bool.mp(th, hth), p, g.1))]),
            @list.List([vc_tac(sym), sym_tac(sym)]),
          )(g)
        } else {
          seq([renorm, step_tac(th, p, g.1), sym_tac(sym)])(g)
        }
      }
    }
  }
}

///|
/// sl_step_l with the instruction's rule `th`, whose precondition must be
/// the goal's `p`.
fn step_tac(th : @kernel.Thm, p : @kernel.Term, goal : @kernel.Term) -> @tactics.Tactic raise {
  guard args_of(@kernel.concl(th), "sl_triple", 3) is Some([p2, code, _]) else {
    raise Failure("step_tac: " + show(@kernel.concl(th)))
  }
  if !@basics.aconv(p, p2) {
    raise Failure("certimoon/logic: sym: the rule's precondition " + show(p2) + " is not the state " + show(p))
  }
  let step = @drule.match_mp(rule_of(goal, "sl_step_l"))(th)
  if is_g(goal) {
    // the instruction has no calls
    let cf = @tactics.prove(@basics.list_mk_comb(tm("call_free_b"), @list.List([code])), call_free_tac())
    @tactics.match_mp_tac(@drule.match_mp(step)(cf))
  } else {
    @tactics.match_mp_tac(step)
  }
}

///|
/// The number of arguments of the spec G(a, P, Q): P says args is a list.
fn spec_arity(spec : @kernel.Thm) -> Int raise {
  let (_, sargs) = @basics.strip_comb(@kernel.concl(spec))
  let pp = sargs.to_array()[sargs.length() - 2]
  let (bvs, body) = @basics.strip_abs(pp)
  guard bvs.to_array() is [args, _, _, _] else { raise Failure("certimoon/logic: sym: not a spec: " + show(pp)) }
  for c in @basics.conjuncts(body) {
    if args_of(c, "=", 2) is Some([a, b]) && a == args && @basics.is_list(b) {
      return @basics.dest_list(b).length()
    }
  }
  raise Failure("certimoon/logic: sym: the spec's P does not give its arguments: " + show(pp))
}

///|
/// For a call in state p: the number of arguments, and the theorem
/// G(a, P, Q) of a spec in sym.specs whose P takes the arguments on
/// top of p's stack, its variables chosen to match them, and its frame
/// (a variable R applied to gs, ms and h) the state's.
fn call_spec(
  sym : Sym,
  goal : @kernel.Term,
  instr : @kernel.Term,
  p : @kernel.Term,
  rule_name? : String = "sl_call_st",
) -> (Int, @kernel.Thm) raise {
  guard args_of(p, "st", 3) is Some([s, _, r]) else { raise Failure("call_spec") }
  let avoid = @kernel.frees(goal)
  for spec in sym.specs {
    let th = fresh_spec(spec, avoid)
    let (_, sargs) = @basics.strip_comb(@kernel.concl(th))
    let sargs = sargs.to_array()
    if sargs.length() < 3 {
      continue
    }
    let pp = sargs[sargs.length() - 2]
    let (bvs, body) = @basics.strip_abs(pp)
    guard bvs.to_array() is [args, gs, ms, h] else { continue }
    let mut pat : @kernel.Term? = None
    let mut frame : @kernel.Term? = None
    for c in @basics.conjuncts(body) {
      if args_of(c, "=", 2) is Some([a, b]) && a == args && @basics.is_list(b) {
        pat = Some(b)
      } else if @basics.strip_comb(c) is (Var(_, _) as rv, xs) && xs.to_array() == [gs, ms, h] {
        frame = Some(rv)
      }
    }
    guard pat is Some(pat) else { continue }
    let k = @basics.dest_list(pat).length()
    guard (try Some(split_stack(s, k)) catch { _ => None }) is Some((_, top)) else { continue }
    let actual = @lists.mk_list(@list.List(top), values_ty())
    guard (try Some(@drule.term_match(@list.List([]), pat, actual)) catch { _ => None }) is Some(i) else { continue }
    let th = @drule.instantiate_rule(i, th)
    let th = match frame {
      Some(rv) => @kernel.inst_rule(@list.List([(r, rv)]), th)
      None => th
    }
    // the spec's function must be the call's
    let rule = rule_of(goal, rule_name)
    guard (try Some(@drule.match_mp(rule)(th)) catch { _ => None }) is Some(_) else { continue }
    return (k, th)
  }
  raise Failure("certimoon/logic: sym: no spec for " + show(instr) + " from " + show(p))
}

///|
/// Whether `t` has an ∃ among its conjuncts.
fn has_exists(t : @kernel.Term) -> Bool {
  if @basics.is_exists(t) {
    return true
  }
  if @basics.is_conj(t) {
    let (a, b) = @basics.dest_conj(t) catch { _ => return false }
    return has_exists(a) || has_exists(b)
  }
  false
}

///|
/// One step towards an exact state, for a precondition λ vs lc gs ms h.
/// body whose conjuncts say vs == v, lc == l, facts (about neither), and
/// the rest (about gs, ms and h): pulls the ∃s to the front, takes them as
/// variables (sl_ex_l), writes the conjuncts as facts && st(v, l, R), and
/// takes the facts as assumptions (sl_pure_l).
fn intro_tac() -> @tactics.Tactic {
  g => {
    let (p, bs, q, ls) = triple_l_terms(g.1)
    let (bvs, body) = @basics.strip_abs(p)
    guard bvs.to_array() is [vs, lc, gs, ms, h] else {
      raise Failure("certimoon/logic: sym: the precondition is not an assertion: " + show(p))
    }
    if @basics.is_exists(body) {
      let (x, b) = @basics.dest_exists(body)
      let pp = @basics.list_mk_abs(bvs.prepend(x), b)
      let th = @equal.beta_rule(@bool.ispecl(@list.List([pp, bs, q, ls]), rule_of(g.1, "sl_ex_l")))
      return seq([@tactics.match_mp_tac(th), @tactics.gen_tac])(g)
    }
    if has_exists(body) {
      let rw = @simp.pure_rewrite_conv(ths([@theorems.left_and_exists_thm(), @theorems.right_and_exists_thm()]))
      return @tactics.conv_tac(pre_conv(rw))(g)
    }
    let mentions = (t : @kernel.Term, v : @kernel.Term) => @basics.free_in(v, t)
    let pure = (t : @kernel.Term) => ![vs, lc, gs, ms, h].iter().any(v => mentions(t, v))
    // facts && st(v, l, R)(vs, lc, gs, ms, h): the facts become assumptions
    if @basics.is_conj(body) {
      let (c, rest) = @basics.dest_conj(body)
      if pure(c) && args_of(rest, "st", 8) is Some(args) && args[3:].to_owned() == bvs.to_array() {
        let facts = if is_g(g.1) { subst_facts_tac() } else { @tactics.disch_then(th => @tactics.strip_assume_tac(th)) }
        return seq([@tactics.match_mp_tac(rule_of(g.1, "sl_pure_l")), facts])(g)
      }
    }
    let conjs = @basics.conjuncts(body).to_array()
    let mut stack : @kernel.Term? = None
    let mut locals : @kernel.Term? = None
    let facts = []
    let rest = []
    for c in conjs {
      if args_of(c, "=", 2) is Some([a, b]) && a == vs && !mentions(b, vs) {
        stack = Some(b)
      } else if args_of(c, "=", 2) is Some([a, b]) && a == lc && !mentions(b, lc) {
        locals = Some(b)
      } else if pure(c) {
        facts.push(c)
      } else if !mentions(c, vs) && !mentions(c, lc) {
        rest.push(c)
      } else {
        raise Failure("certimoon/logic: sym: cannot read " + show(c) + " as part of a state")
      }
    }
    guard stack is Some(s) && locals is Some(l) else {
      raise Failure("certimoon/logic: sym: the precondition does not fix the stack and locals: " + show(p))
    }
    let rbody = if rest.is_empty() { tm("T") } else { @bool.list_mk_conj(@list.List(rest)) }
    let r = @basics.list_mk_abs(@list.List([gs, ms, h]), rbody)
    let r = @equal.rhs(@kernel.concl(norm_conv()(r)))
    let state = @basics.list_mk_comb(tm("st"), @list.List([s, l, r]))
    let p2 = if facts.is_empty() {
      state
    } else {
      let applied = @basics.list_mk_comb(state, bvs)
      @basics.list_mk_abs(bvs, @bool.mk_conj(@bool.list_mk_conj(@list.List(facts)), applied))
    }
    @tactics.thenl(
      seq([@tactics.match_mp_tac(rule_of(g.1, "sl_pre_l")), @tactics.exists_tac(p2), @tactics.conj_tac]),
      @list.List([
        // the same conjuncts, rearranged
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @simp.rewrite_tac(ths([thm("st")])),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @simp.asm_rewrite_tac(ths([])),
          // the state's R is written out: so are the facts it came from
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm_thms()))),
          @simp.asm_rewrite_tac(ths([])),
          g => raise Failure("certimoon/logic: sym: cannot rearrange the precondition: " + show(g.1)),
        ]),
        @tactics.all_tac,
      ]),
    )(g)
  }
}

///|
/// Takes the facts as assumptions, and substitutes those that say a
/// variable is a term (a function's arguments).
fn subst_facts_tac() -> @tactics.Tactic {
  @tactics.disch_then(th => g => {
    let parts = @bool.conjuncts_rule(th).to_array()
    let tacs = parts.map(c => {
      let t = @kernel.concl(c)
      if args_of(t, "=", 2) is Some([Var(_, _) as v, b]) && !@basics.free_in(v, b) {
        @tactics.subst_var_tac(c)
      } else {
        @tactics.strip_assume_tac(c)
      }
    })
    seq(tacs)(g)
  })
}

///|
/// The Loop instructions in `code`, and the Block, If and Loop
/// instructions with more code after them, each outermost and first first.
fn structure_of(code : @kernel.Term) -> (Array[@kernel.Term], Array[@kernel.Term]) raise {
  let loops = []
  let afters = []
  fn walk(t : @kernel.Term) -> Unit raise {
    if !@basics.is_list(t) {
      return
    }
    let instrs = @basics.dest_list(t).to_array()
    for k, i in instrs {
      let (_, args) = @basics.strip_comb(i)
      let name = head_name(i)
      if k + 1 < instrs.length() && (name == "Block" || name == "If" || name == "Loop") {
        afters.push(i)
      }
      match name {
        "Loop" => {
          loops.push(i)
          walk(args.to_array()[1])
        }
        "Block" => walk(args.to_array()[1])
        "If" => {
          walk(args.to_array()[1])
          walk(args.to_array()[2])
        }
        _ => ()
      }
    }
  }
  walk(code)
  (loops, afters)
}

///|
/// Proves `stmt` by running its code (sym_tac), and records it as `name`.
///
/// `stmt` is `∀ xs. hyps → sl_triple(p, code, q)` (code without calls),
/// or `∀ xs. hyps → sl_triple_g(G, fs, tabs, inst, rp, p, code, q, ls)` (a
/// function's body, or any code with calls and returns). The code may be
/// a program's name (`program`): its definition is unfolded first.
///
/// - `invs`: the invariants of code's loops, in order (outermost and first
///   first), each `λ lc gs ms h. ...` (for the locals, globals, memory
///   length and heap at the loop's start and at each `br` to it);
/// - `vcs`: one tactic for each condition sym_tac leaves, in order (with
///   the wrong number, the error lists the conditions and what each
///   tactic leaves);
/// - `afters`: the state after each block, if or loop that has more code
///   after it, in the same order as `invs`, each `λ vs lc gs ms h. ...`;
/// - `rules`: the st_ rules for straight-line instructions, tried in order;
/// - `rws`: more rewrites for the conditions (before they are left);
/// - `specs`: for calls, theorems `∀ xs. G(a, P, Q)`; a call uses the first
///   whose P (of the form `args == [...] && R(gs, ms, h)`) matches the
///   stack, with R the state's;
/// - `calls`: for each call in order, if given, a spec (its index in
///   `specs`) and the terms for its ∀s: the call then leaves "P of its
///   arguments" to prove, and the code after it starts from Q;
/// - `kind`: how load()'s listing shows it ("example" or "lemma").
#callsite(autofill(loc))
pub fn sym_prove(
  name : String,
  stmt : String,
  invs : Array[String],
  vcs : Array[@tactics.Tactic],
  afters? : Array[String] = [],
  rules? : Array[String] = step_rules,
  rws? : Array[@kernel.Thm] = [],
  specs? : Array[@kernel.Thm] = [],
  calls? : Array[(Int, Array[String])] = [],
  kind? : String = "example",
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  let goal = tm(stmt)
  let (_, body) = @basics.strip_forall(goal)
  let triple = if @basics.is_imp(body) { @basics.dest_imp(body).1 } else { body }
  let (code, g) = match (args_of(triple, "sl_triple", 3), args_of(triple, "sl_triple_g", 9)) {
    (Some([_, code, _]), _) => (code, false)
    (_, Some(args)) => (args[6], true)
    _ => raise Failure("certimoon/logic: sym_prove: not a triple: " + show(triple))
  }
  // a program's name: run its code
  let (code, unfold) = match program_def(code) {
    Some(d) => (@kernel.dest_eq(@kernel.concl(@simp.pure_rewrite_conv(ths([d]))(code))).1, [d])
    None => (code, [])
  }
  let (loops, after) = structure_of(code)
  if loops.length() != invs.length() || after.length() != afters.length() {
    raise Failure(
      "certimoon/logic: sym_prove " + name + ": " + loops.length().to_string() + " loops, " +
      invs.length().to_string() + " invariants, " + after.length().to_string() +
      " blocks with code after them, " + afters.length().to_string() + " states after",
    )
  }
  let sym = {
    loops: loops.mapi((k, l) => (l, tm(invs[k]))),
    afters: after.mapi((k, a) => (a, tm(afters[k]))),
    rules,
    rws,
    specs,
    calls,
    next_call: Ref::{ val: 0 },
  }
  let run = seq([
    g => {
      // the calls' specs are taken in order from the start
      sym.next_call.val = 0
      @tactics.all_tac(g)
    },
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.try_tac(@tactics.disch_then(th => @tactics.strip_assume_tac(th))),
    @simp.pure_rewrite_tac(ths(unfold)),
    if g { beta_goal() } else { @tactics.match_mp_tac(thm("sl_triple_of_l")) },
    sym_tac(sym),
  ])
  let th = @tactics.prove(goal, @tactics.thenl(run, @list.List(vcs))) catch {
    e => {
      // say what is left
      let left = (try run((@list.List([]), goal)) catch { _ => raise e }).1
      let msg = StringBuilder()
      msg.write_string("certimoon/logic: sym_prove " + name + ": " + e.to_string() + "; ")
      msg.write_string(left.length().to_string() + " goals left (" + vcs.length().to_string() + " tactics):")
      let goal_text = (gl : @tactics.Goal) => {
        let b = StringBuilder()
        for a in gl.0 {
          b.write_string("\n  [" + a.0 + "] " + show(@kernel.concl(a.1)))
        }
        b.write_string("\n  ⊢ " + show(gl.1))
        b.to_string()
      }
      let gls = left.to_array()
      for k, gl in gls {
        // with as many tactics as goals, say which tactic fails
        let verdict = if gls.length() != vcs.length() {
          ""
        } else {
          let result : Result[@list.List[@tactics.Goal], Error] = try Ok(vcs[k](gl).1) catch {
            e => Err(e)
          }
          match result {
            Ok(after) if after.is_empty() => " (its tactic proves it)"
            Ok(after) => " (its tactic leaves:" + after.to_array().map(goal_text).join("") + "\n  )"
            Err(e) => " (its tactic fails: " + e.to_string() + ")"
          }
        }
        msg.write_string("\n-- " + (k + 1).to_string() + verdict + goal_text(gl))
      }
      raise Failure(msg.to_string())
    }
  }
  record(name, th, kind~, loc~)
  th
}
