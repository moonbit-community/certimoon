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
// - for if, block and loop (last in their list), goes into the branches
//   and bodies (sl_if_st, sl_block_st, sl_loop_st), taking the loop's
//   invariant from the caller;
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
let sa_false : String = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => false"

///|
fn prove_sym_rules() -> Unit raise {
  let sa = sassn
  let st = thm("st")
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
    @tactics.match_mp_tac(thm("sl_conseq_l")),
    @tactics.exists_tac(tm(p)),
    @tactics.exists_tac(tm(q)),
    @tactics.exists_tac(tm(ls)),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([solve(triple), solve(simple)])),
  ])
  let _ = lemma(
    "sl_pre_l",
    "∀ p : \{sa}, ∀ p2 : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, p2(vs, lc, gs, ms, h) → p(vs, lc, gs, ms, h)) && sl_triple_l(p, bs, q, ls) → sl_triple_l(p2, bs, q, ls)",
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
  let state = "st((v : List[Value]), (l : List[Value]), (R : \{rty}))"
  let vars = "∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}"
  let ls = "(ls : List[\{sa}])"
  let _ = lemma(
    "sl_nil_st",
    "\{vars}, ∀ r : \{sa}, ∀ ls : List[\{sa}], (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → r(v, l, gs, ms, h)) → sl_triple_l(\{state}, NIL, r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      conseq(state, state, ls, @tactics.match_accept_tac(thm("sl_nil_l"))),
    ]),
  )
  let br_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && EL(i, ls, vb, lc, gs, ms, h))"
  let _ = lemma(
    "sl_br_st",
    "\{vars}, ∀ i : Num, ∀ r : \{sa}, ∀ ls : List[\{sa}], i < LENGTH(ls) && (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → (∃ vs0 : List[Value], ∃ vb : List[Value], v == APPEND(vs0, vb) && EL(i, ls, vb, l, gs, ms, h))) → sl_triple_l(\{state}, [Br(i)], r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      conseq(
        br_pre,
        sa_false,
        ls,
        seq([@tactics.match_mp_tac(thm("sl_br")), @tactics.first_assum(th => @tactics.accept_tac(th))]),
      ),
    ]),
  )
  // the precondition of sl_br_if and sl_if, for p = st(v, l, R)
  let x = "V_num(ConstInt32((c : \{w32})))"
  let pre_c = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [\{x}]) && \{state}(vs0, lc, gs, ms, h))"
  let top = "st(APPEND(v, [\{x}]), l, R)"
  let to_pre_c = (rest : @tactics.Tactic) => seq([
    @tactics.match_mp_tac(thm("sl_pre_l")),
    @tactics.exists_tac(tm(pre_c)),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([solve(@simp.rewrite_tac(ths([thm("st_snoc_ex")]))), rest]),
    ),
  ])
  let _ = lemma(
    "sl_br_if_st",
    "\{vars}, ∀ c : \{w32}, ∀ i : Num, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (!(c == word(0)) → sl_triple_l(\{state}, [Br(i)], \{sa_false}, ls)) && (c == word(0) → sl_triple_l(\{state}, rest, r, ls)) → sl_triple_l(\{top}, CONS(Br_if(i), rest), r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.subst1_tac(cons_append("Br_if((i : Num))", "(rest : List[B_e])")),
      @tactics.match_mp_tac(thm("sl_seq_l")),
      @tactics.exists_tac(
        tm("(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (c : \{w32}) == word(0) && \{state}(vs, lc, gs, ms, h)"),
      ),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          to_pre_c(
            @tactics.thenl(
              seq([@tactics.match_mp_tac(thm("sl_br_if")), @tactics.conj_tac]),
              @list.List([
                // c ≠ 0: br, whose postcondition is false
                seq([@tactics.disch_tac, conseq(state, sa_false, ls, @meson.asm_meson_tac(ths([])))]),
                seq([@tactics.disch_tac, @tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))]),
              ]),
            ),
          ),
          seq([
            @tactics.match_mp_tac(thm("sl_pure_l")),
            @simp.rewrite_tac(ths([@class.eta_ax()])),
            @tactics.first_assum(th => @tactics.accept_tac(th)),
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "sl_if_st",
    "\{vars}, ∀ c : \{w32}, ∀ tb : Tb, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (!(c == word(0)) → sl_triple_l(\{state}, [Block(tb, bs1)], r, ls)) && (c == word(0) → sl_triple_l(\{state}, [Block(tb, bs2)], r, ls)) → sl_triple_l(\{top}, [If(tb, bs1, bs2)], r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      to_pre_c(
        seq([
          @tactics.match_mp_tac(thm("sl_if")),
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
    @bool.ispecl(
      @list.List(
        [ot, "(bs : List[B_e])", "st((NIL : List[Value]), l, R)", after, lb, ls, "(v : List[Value])"].map(tm),
      ),
      thm("sl_block"),
    ),
  )
  let (_, block_concl) = @basics.dest_imp(@kernel.concl(block))
  let (block_pre, _, block_post, _) = triple_l_terms(block_concl)
  let _ = lemma(
    "sl_block_st",
    "\{vars}, ∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], sl_triple_l(st(NIL, l, R), bs, \{after}, CONS(\{lb}, ls)) → sl_triple_l(\{state}, [Block(Tbv(ot), bs)], r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_conseq_l")),
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
  let looped = @equal.beta_rule(
    @bool.ispecl(
      @list.List([ot, "(bs : List[B_e])", linv, after, ls, "(v : List[Value])"].map(tm)),
      thm("sl_loop"),
    ),
  )
  let (_, loop_concl) = @basics.dest_imp(@kernel.concl(looped))
  let (loop_pre, _, loop_post, _) = triple_l_terms(loop_concl)
  let _ = lemma(
    "sl_loop_st",
    "∀ linv : (List[Value], List[Value], Num, \{heap}) -> Bool, \{vars}, ∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → linv(l, gs, ms, h)) && sl_triple_l(\{lbl}, bs, \{after}, CONS(\{lbl}, ls)) → sl_triple_l(\{state}, [Loop(Tbv(ot), bs)], r, ls)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("sl_conseq_l")),
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

// ---------------------------------------------------------------------------
// The tactic.
// ---------------------------------------------------------------------------

///|
/// What `sym_tac` needs besides the goal: the loops' invariants (each
/// Loop instruction with its linv) and rewrites for the verification
/// conditions.
priv struct Sym {
  loops : Array[(@kernel.Term, @kernel.Term)]
  rws : Array[@kernel.Thm]
}

///|
/// The arguments of `name` applied to `n` arguments, if `t` is that.
fn args_of(t : @kernel.Term, name : String, n : Int) -> Array[@kernel.Term]? {
  let (f, args) = @basics.strip_comb(t)
  match f {
    Const(c, _) if c == name && args.length() == n => Some(args.to_array())
    _ => None
  }
}

///|
/// The name of the constructor at the head of `t`.
fn head_name(t : @kernel.Term) -> String {
  match @basics.strip_comb(t).0 {
    Const(c, _) => c
    _ => ""
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
    raise Failure("wasmcert/logic: sym: the stack " + show(s) + " has fewer than " + k.to_string() + " values on top")
  }
  let below = @lists.mk_list(@list.List(elems[0:n - k].to_owned()), values_ty())
  let prefix = match base {
    None => below
    Some(b) => if n == k { b } else { mk_append(b, below) }
  }
  (prefix, elems[n - k:].to_owned())
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
      raise Failure("wasmcert/logic: sym: cannot split the stack " + show(s))
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
let step_rules : Array[String] = [
  "st_const", "st_binop", "st_testop", "st_relop", "st_local_get", "st_local_set",
  "st_arr_store", "st_arr_load",
]

///|
/// The rule for `instr` from the state st(s, l, r): sl_triple(st(s, l, r),
/// [instr], post), written out, after a side condition if it keeps one.
fn step_rule(instr : @kernel.Term, p : @kernel.Term) -> @kernel.Thm raise {
  guard args_of(p, "st", 3) is Some([s, l, r]) else { raise Failure("step_rule") }
  let avoid = @kernel.frees(p) + @kernel.frees(instr)
  for name in step_rules {
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
  raise Failure("wasmcert/logic: sym: no rule for " + show(instr) + " from " + show(p))
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
    raise Failure("wasmcert/logic: sym: " + show(x) + " is " + show(computed) + ", not SOME of a value")
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
fn beta_goal() -> @tactics.Tactic {
  @tactics.conv_tac(@equal.try_conv(@equal.redepth_conv(@equal.beta_conv)))
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
      return seq([renorm, @tactics.match_mp_tac(thm("sl_nil_st")), vc_tac(sym)])(g)
    }
    guard args_of(code, "CONS", 2) is Some([instr, rest]) else {
      raise Failure("wasmcert/logic: sym: the code is not a list: " + show(code))
    }
    let last = @basics.is_list(rest) && @basics.dest_list(rest).is_empty()
    let need_last = (what : String) => if !last {
      raise Failure("wasmcert/logic: sym: " + what + " must end its instruction list")
    }
    match head_name(instr) {
      "Br" => {
        need_last("br")
        seq([renorm, @tactics.match_mp_tac(thm("sl_br_st")), @tactics.conj_tac, vc_tac(sym)])(g)
      }
      "Br_if" =>
        seq([
          renorm,
          split_tac(1),
          @tactics.match_mp_tac(thm("sl_br_if_st")),
          @tactics.conj_tac,
          fact_tac(),
          sym_tac(sym),
        ])(g)
      "If" => {
        need_last("if")
        seq([
          renorm,
          split_tac(1),
          @tactics.match_mp_tac(thm("sl_if_st")),
          @tactics.conj_tac,
          fact_tac(),
          sym_tac(sym),
        ])(g)
      }
      "Block" => {
        need_last("block")
        seq([renorm, @tactics.match_mp_tac(thm("sl_block_st")), beta_goal(), sym_tac(sym)])(g)
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
          raise Failure("wasmcert/logic: sym: no invariant for " + show(instr))
        }
        @tactics.thenl(
          seq([renorm, @tactics.match_mp_tac(@bool.ispec(inv, thm("sl_loop_st"))), beta_goal(), @tactics.conj_tac]),
          @list.List([vc_tac(sym), sym_tac(sym)]),
        )(g)
      }
      _ => {
        let th = step_rule(instr, p)
        let c = @kernel.concl(th)
        if @basics.is_imp(c) {
          let (h, _) = @basics.dest_imp(c)
          @tactics.thenl(
            seq([renorm, @tactics.subgoal_then(h, hth => step_tac(@bool.mp(th, hth), p))]),
            @list.List([vc_tac(sym), sym_tac(sym)]),
          )(g)
        } else {
          seq([renorm, step_tac(th, p), sym_tac(sym)])(g)
        }
      }
    }
  }
}

///|
/// sl_step_l with the instruction's rule `th`, whose precondition must be
/// the goal's `p`.
fn step_tac(th : @kernel.Thm, p : @kernel.Term) -> @tactics.Tactic raise {
  guard args_of(@kernel.concl(th), "sl_triple", 3) is Some([p2, _, _]) else {
    raise Failure("step_tac: " + show(@kernel.concl(th)))
  }
  if !@basics.aconv(p, p2) {
    raise Failure("wasmcert/logic: sym: the rule's precondition " + show(p2) + " is not the state " + show(p))
  }
  @tactics.match_mp_tac(@drule.match_mp(thm("sl_step_l"))(th))
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
      raise Failure("wasmcert/logic: sym: the precondition is not an assertion: " + show(p))
    }
    if @basics.is_exists(body) {
      let (x, b) = @basics.dest_exists(body)
      let pp = @basics.list_mk_abs(bvs.prepend(x), b)
      let th = @equal.beta_rule(@bool.ispecl(@list.List([pp, bs, q, ls]), thm("sl_ex_l")))
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
        return seq([
          @tactics.match_mp_tac(thm("sl_pure_l")),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        ])(g)
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
        raise Failure("wasmcert/logic: sym: cannot read " + show(c) + " as part of a state")
      }
    }
    guard stack is Some(s) && locals is Some(l) else {
      raise Failure("wasmcert/logic: sym: the precondition does not fix the stack and locals: " + show(p))
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
      seq([@tactics.match_mp_tac(thm("sl_pre_l")), @tactics.exists_tac(p2), @tactics.conj_tac]),
      @list.List([
        // the same conjuncts, rearranged
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @simp.rewrite_tac(ths([thm("st")])),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @simp.asm_rewrite_tac(ths([])),
          g => raise Failure("wasmcert/logic: sym: cannot rearrange the precondition: " + show(g.1)),
        ]),
        @tactics.all_tac,
      ]),
    )(g)
  }
}

///|
/// mp_tac of `th` (∀ xs. a → b) at `args`, a from the assumptions, and b
/// taken apart into assumptions: for verification conditions.
fn by_lemma(th : @kernel.Thm, args : Array[String]) -> @tactics.Tactic raise {
  seq([
    @tactics.mp_tac(@bool.ispecl(@list.List(args.map(tm)), th)),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@tactics.disch_then(th => @tactics.strip_assume_tac(th))),
  ])
}

///|
/// The Loop instructions in `code`, outermost and first first.
fn loops_in(code : @kernel.Term) -> Array[@kernel.Term] raise {
  let out = []
  fn walk(t : @kernel.Term) -> Unit raise {
    if !@basics.is_list(t) {
      return
    }
    for i in @basics.dest_list(t) {
      let (_, args) = @basics.strip_comb(i)
      match head_name(i) {
        "Loop" => {
          out.push(i)
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
  out
}

///|
/// Proves `stmt` (∀ xs. hyps → sl_triple(p, code, q)) by sym_tac, with
/// `invs` the invariants (linv, λ lc gs ms h. ...) of code's loops in
/// order, and `vcs` the tactics for what sym_tac leaves, in order.
/// Records it as `name`.
fn sym_prove(
  name : String,
  stmt : String,
  invs : Array[String],
  vcs : Array[@tactics.Tactic],
  rws? : Array[@kernel.Thm] = [],
  kind? : String = "example",
) -> @kernel.Thm raise {
  let goal = tm(stmt)
  let (_, body) = @basics.strip_forall(goal)
  let triple = if @basics.is_imp(body) { @basics.dest_imp(body).1 } else { body }
  guard args_of(triple, "sl_triple", 3) is Some([_, code, _]) else {
    raise Failure("wasmcert/logic: sym_prove: not a triple: " + show(triple))
  }
  let loops = loops_in(code)
  if loops.length() != invs.length() {
    raise Failure(
      "wasmcert/logic: sym_prove " + name + ": " + loops.length().to_string() + " loops, " +
      invs.length().to_string() + " invariants",
    )
  }
  let sym = { loops: loops.mapi((k, l) => (l, tm(invs[k]))), rws }
  let run = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.try_tac(@tactics.disch_then(th => @tactics.strip_assume_tac(th))),
    @tactics.match_mp_tac(thm("sl_triple_of_l")),
    sym_tac(sym),
  ])
  let th = @tactics.prove(goal, @tactics.thenl(run, @list.List(vcs))) catch {
    e => {
      // say what is left
      let left = (try run((@list.List([]), goal)) catch { _ => raise e }).1
      let msg = StringBuilder()
      msg.write_string("wasmcert/logic: sym_prove " + name + ": " + e.to_string() + "; ")
      msg.write_string(left.length().to_string() + " goals left (" + vcs.length().to_string() + " tactics):")
      for gl in left {
        msg.write_string("\n--")
        for a in gl.0 {
          msg.write_string("\n  [" + a.0 + "] " + show(@kernel.concl(a.1)))
        }
        msg.write_string("\n  ⊢ " + show(gl.1))
      }
      raise Failure(msg.to_string())
    }
  }
  record(name, th, kind~)
  th
}
