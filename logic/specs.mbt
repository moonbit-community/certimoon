// Module triples with returns and function specs.
//
// - G, a set of function specs: G(a, P, Q) says that the function at
//   address a of the store, given arguments args with P(args, gs, ms, h),
//   returns results res with Q(res, gs, ms, h) (gs, ms and h as in an
//   assertion, for the module's instance).
// - inv_ok(n, fs, inst, a, P, Q): invoking a from arguments with P is
//   safe, for n steps or fewer, and ends in results with Q; the caller's
//   stack below the arguments and its locals are kept. specs_ok(n, G, fs,
//   inst): so is every spec of G.
// - sl_triple_g(G, fs, inst, rp, p, bs, q, ls): for every n, when the
//   specs of G hold for n steps, bs is safe for n steps, as a module
//   triple (fs and inst kept), with label assertions ls and return
//   assertion rp. A triple holds for n steps only while G's specs do, so
//   a function's body may be proved assuming its own spec (sl_funs_g):
//   a call takes a step before its body runs, and the induction on n
//   goes through.
//
// sl_funs_g proves G's specs from their bodies' triples; sl_triple_m_of_g
// then drops G (and the return assertion, which must be false outside
// a function). Every module triple is one of these (sl_triple_g_of_m), so
// call-free code's triples are too (sl_triple_g_of).

///|
/// The functions' pre- and postconditions: on the arguments (or
/// results), the globals, the memory's length and the heap.
let fprop : String = "(List[Value], List[Value], Num, \{heap}) -> Bool"

///|
/// A set of function specs.
let specs_ty : String = "(Num, \{fprop}, \{fprop}) -> Bool"

///|
/// The precondition of a call: the arguments on top of vs0, the locals lc0.
fn call_pre(p : String, vs0 : String, lc0 : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ args : List[Value], vs == APPEND(\{vs0}, args) && lc == \{lc0} && \{p}(args, gs, ms, h)"
}

///|
/// The postcondition of a call: the results on top of vs0, the locals lc0.
fn call_post(q : String, vs0 : String, lc0 : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ res : List[Value], vs == APPEND(\{vs0}, res) && lc == \{lc0} && \{q}(res, gs, ms, h)"
}

///|
/// A function body's precondition: no values, the arguments and zeros
/// as locals.
fn body_pre(p : String, args : String, zs : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == APPEND(\{args}, \{zs}) && \{p}(\{args}, gs, ms, h)"
}

///|
/// A function body's postcondition (and its label's, and its return's).
fn body_post(q : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{q}(vs, gs, ms, h)"
}

///|
/// The triple sl_triple_g(G, fs, inst, rp, p, bs, q, ls).
fn triple_g(p : String, bs : String, q : String, ls : String) -> String {
  "sl_triple_g(G, fs, inst, rp, \{p}, \{bs}, \{q}, \{ls})"
}

///|
/// The quantifiers for G, fs, inst and rp.
fn env_vars() -> String {
  "∀ G : \{specs_ty}, ∀ fs : List[Cl], ∀ inst : Inst, ∀ rp : \{sassn}, "
}

///|
fn define_specs() -> Unit raise {
  let a = assn
  let sa = sassn
  def(
    "inv_ok",
    "inv_ok((n : Num), (fs : List[Cl]), (inst : Inst), (a : Num), (P : \{fprop}), (Q : \{fprop})) == (∀ m : Num, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ stk : List[Value], ∀ vs0 : List[Value], ∀ lc0 : List[Value], ∀ l : List[\{a}], ∀ rq : \{a}, m <= n && keep(fs, inst, lift(\{call_pre("P", "vs0", "lc0")}, fr), s, f, stk) → safer(m, s, f, APPEND(MAP(v_to_e, stk), [Invoke(a)]), keep(fs, inst, lift(\{call_post("Q", "vs0", "lc0")}, fr)), l, rq))",
  )
  def(
    "specs_ok",
    "specs_ok((n : Num), (G : \{specs_ty}), (fs : List[Cl]), (inst : Inst)) == (∀ a : Num, ∀ P : \{fprop}, ∀ Q : \{fprop}, G(a, P, Q) → inv_ok(n, fs, inst, a, P, Q))",
  )
  def(
    "sl_triple_g",
    "sl_triple_g((G : \{specs_ty}), (fs : List[Cl]), (inst : Inst), (rp : \{sa}), (p : \{sa}), (bs : List[B_e]), (q : \{sa}), (ls : List[\{sa}])) == (∀ n : Num, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], specs_ok(n, G, fs, inst) && keep(fs, inst, lift(p, fr), s, f, vs) → safer(n, s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs)), keep(fs, inst, lift(q, fr)), MAP(keep(fs, inst), MAP((x : \{sa}) => lift(x, fr), ls)), keep(fs, inst, lift(rp, fr))))",
  )
}

///|
/// Proves call_free_b of written-out code.
fn call_free_tac() -> @tactics.Tactic raise {
  seq([
    @simp.rewrite_tac(ths([thm("call_free_b"), @lists.all()])),
    @tactics.conv_tac(@equal.top_depth_conv(has_call_conv())),
    @simp.rewrite_tac(ths([])),
  ])
}

///|
/// The g triples' basic rules: from module triples, sequencing,
/// consequence, the empty program, ∃ and pure facts, br, false.
fn prove_specs_basics() -> Unit raise {
  let sa = sassn
  let sl_triple_g = thm("sl_triple_g")
  let keep = thm("keep")
  let env = env_vars()
  let fr = "(fr : \{hprop})"
  let _ = lemma(
    "specs_down",
    "∀ n : Num, ∀ m : Num, ∀ G : \{specs_ty}, ∀ fs : List[Cl], ∀ inst : Inst, m <= n && specs_ok(n, G, fs, inst) → specs_ok(m, G, fs, inst)",
    seq([
      @simp.rewrite_tac(ths([thm("specs_ok"), thm("inv_ok")])),
      @meson.meson_tac(ths([@arith.le_trans()])),
    ]),
  )
  let _ = lemma(
    "sl_triple_g_of_m",
    "\{env}∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], sl_triple_m(fs, inst, p, bs, q, ls) → \{triple_g("p", "bs", "q", "ls")}",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple_m"), sl_triple_g, thm("triple_l")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safel_safer")),
      @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ]),
  )
  let _ = lemma(
    "sl_triple_g_of",
    "\{env}∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], call_free_b(bs) && sl_triple_l(p, bs, q, ls) → \{triple_g("p", "bs", "q", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("sl_triple_g_of_m")),
      @tactics.match_mp_tac(thm("sl_triple_m_of")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_triple_m_of_g",
    "∀ G : \{specs_ty}, ∀ fs : List[Cl], ∀ inst : Inst, ∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], (∀ n : Num, specs_ok(n, G, fs, inst)) && sl_triple_g(G, fs, inst, \{sa_false}, p, bs, q, ls) → sl_triple_m(fs, inst, p, bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([thm("sl_triple_m"), sl_triple_g, thm("triple_l")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safer_safel")),
      @tactics.exists_tac(
        tm("keep(fs, inst, lift(\{sa_false}, (r : \{hprop})))"),
      ),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@simp.rewrite_tac(ths([keep, thm("lift"), thm("star")]))]),
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "sl_seq_g",
    "\{env}∀ p : \{sa}, ∀ bs1 : List[B_e], ∀ q : \{sa}, ∀ bs2 : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], \{triple_g("p", "bs1", "q", "ls")} && \{triple_g("q", "bs2", "r", "ls")} → \{triple_g("p", "APPEND(bs1, bs2)", "r", "ls")}",
    seq([
      @simp.rewrite_tac(
        ths([sl_triple_g, @lists.map_append(), @lists.append_assoc()]),
      ),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safer_seq")),
      @tactics.exists_tac(tm("keep(fs, inst, lift((q : \{sa}), \{fr}))")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.match_mp_tac(thm("specs_down")),
            @tactics.exists_tac(tm("(n : Num)")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  let lift_l = "MAP(keep(fs, inst), MAP((x : \{sa}) => lift(x, \{fr}), (ls : List[\{sa}])))"
  let ent = (x : String, y : String) => {
    "(∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{x}(vs, lc, gs, ms, h) → \{y}(vs, lc, gs, ms, h))"
  }
  // keep(fs, inst, lift(x, fr), s, f, v) from keep(fs, inst, lift(y, fr), s, f, v)
  let keep_mono_at = (y : String, v : String) => {
    seq([
      @tactics.disch_tac,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([keep]))),
      split_conjs(),
      @simp.asm_rewrite_tac(ths([keep])),
      @tactics.match_mp_tac(thm("lift_mono")),
      @tactics.exists_tac(tm(y)),
      @tactics.exists_tac(tm(v)),
      @meson.asm_meson_tac(ths([])),
    ])
  }
  let gen3 = seq([
    @tactics.x_gen_tac(tm("(s2 : Wstore)")),
    @tactics.x_gen_tac(tm("(f2 : Wframe)")),
    @tactics.x_gen_tac(tm("(vs2 : List[Value])")),
  ])
  let keep_mono = (y : String) => {
    seq([gen3, keep_mono_at(y, "(vs2 : List[Value])")])
  }
  let _ = lemma(
    "sl_conseq_g",
    "\{env}∀ p : \{sa}, ∀ p2 : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ q2 : \{sa}, ∀ ls : List[\{sa}], ∀ ls2 : List[\{sa}], \{ent("p2", "p")} && \{triple_g("p", "bs", "q", "ls")} && \{ent("q", "q2")} && LENGTH(ls2) == LENGTH(ls) && (∀ i : Num, ∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, i < LENGTH(ls) && EL(i, ls, vs, lc, gs, ms, h) → EL(i, ls2, vs, lc, gs, ms, h)) → \{triple_g("p2", "bs", "q2", "ls2")}",
    seq([
      @simp.rewrite_tac(ths([sl_triple_g])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safer_mono")),
      @tactics.exists_tac(tm("keep(fs, inst, lift((q : \{sa}), \{fr}))")),
      @tactics.exists_tac(tm(lift_l)),
      @tactics.exists_tac(tm("keep(fs, inst, lift((rp : \{sa}), \{fr}))")),
      @simp.asm_rewrite_tac(ths([@lists.length_map()])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          // the return assertion is the same
          solve(
            seq([
              @tactics.repeat_tac(@tactics.strip_tac),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
          // the postcondition
          solve(keep_mono("(q : \{sa})")),
          // each label
          solve(
            seq([
              @tactics.x_gen_tac(tm("(i : Num)")),
              gen3,
              @tactics.disch_then(th => {
                @tactics.conjuncts_then2(a => @tactics.assume_tac(a), b => {
                  @tactics.mp_tac(b)
                })(th)
              }),
              @tactics.rule_assum_tac(
                @simp.rewrite_rule(ths([@lists.length_map()])),
              ),
              have(
                "(i : Num) < LENGTH((ls2 : List[\{sa}]))",
                @simp.asm_rewrite_tac(ths([])),
              ),
              @simp.asm_simp_tac(ths([@lists.el_map(), @lists.length_map()])),
              @tactics.disch_tac,
              @tactics.rule_assum_tac(@simp.rewrite_rule(ths([keep]))),
              split_conjs(),
              @simp.asm_rewrite_tac(ths([keep])),
              @tactics.match_mp_tac(thm("lift_mono")),
              @tactics.exists_tac(tm("EL((i : Num), (ls : List[\{sa}]))")),
              @tactics.exists_tac(tm("(vs2 : List[Value])")),
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
          // the triple, from the stronger precondition
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                @tactics.first_assum(th => @tactics.accept_tac(th)),
                seq([
                  @tactics.undisch_tac(
                    tm(
                      "keep(fs, inst, lift((p2 : \{sa}), \{fr}), (s : Wstore), (f : Wframe), (vs : List[Value]))",
                    ),
                  ),
                  keep_mono_at("(p2 : \{sa})", "(vs : List[Value])"),
                ]),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "sl_conseq_ret_g",
    "∀ G : \{specs_ty}, ∀ fs : List[Cl], ∀ inst : Inst, ∀ rp : \{sa}, ∀ rp2 : \{sa}, ∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], \{ent("rp", "rp2")} && \{triple_g("p", "bs", "q", "ls")} → sl_triple_g(G, fs, inst, rp2, p, bs, q, ls)",
    seq([
      @simp.rewrite_tac(ths([sl_triple_g])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safer_mono")),
      @tactics.exists_tac(tm("keep(fs, inst, lift((q : \{sa}), \{fr}))")),
      @tactics.exists_tac(tm(lift_l)),
      @tactics.exists_tac(tm("keep(fs, inst, lift((rp : \{sa}), \{fr}))")),
      @simp.rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.repeat_tac(@tactics.strip_tac),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
          solve(keep_mono("(rp : \{sa})")),
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "sl_nil_g",
    "\{env}∀ p : \{sa}, ∀ ls : List[\{sa}], \{triple_g("p", "NIL", "p", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.match_mp_tac(thm("sl_triple_g_of")),
      @tactics.conj_tac,
      call_free_tac(),
      @tactics.match_accept_tac(thm("sl_nil_l")),
    ]),
  )
  let _ = lemma(
    "sl_false_g",
    "\{env}∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], \{triple_g(sa_false, "bs", "q", "ls")}",
    seq([@simp.rewrite_tac(ths([sl_triple_g, keep, thm("lift"), thm("star")]))]),
  )
  let pp = "(A, List[Value], List[Value], List[Value], Num, \{heap}) -> Bool"
  let _ = lemma(
    "sl_ex_g",
    "\{env}∀ pp : \{pp}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], (∀ x : A, \{triple_g("pp(x)", "bs", "q", "ls")}) → \{triple_g("(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ x : A, pp(x, vs, lc, gs, ms, h))", "bs", "q", "ls")}",
    seq([
      @simp.rewrite_tac(ths([sl_triple_g, keep, thm("lift_ex")])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_pure_g",
    "\{env}∀ c : Bool, ∀ p : \{sa}, ∀ bs : List[B_e], ∀ q : \{sa}, ∀ ls : List[\{sa}], (c → \{triple_g("p", "bs", "q", "ls")}) → \{triple_g("(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => c && p(vs, lc, gs, ms, h)", "bs", "q", "ls")}",
    seq([
      @simp.rewrite_tac(ths([sl_triple_g, keep, thm("lift_pure")])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let br_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && EL(i, ls, vb, lc, gs, ms, h))"
  let _ = lemma(
    "sl_br_g",
    "\{env}∀ i : Num, ∀ ls : List[\{sa}], i < LENGTH(ls) → \{triple_g(br_pre, "[Br(i)]", sa_false, "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("sl_triple_g_of")),
      @tactics.conj_tac,
      call_free_tac(),
      @tactics.match_mp_tac(thm("sl_br")),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ]),
  )
  let ret_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && rp(vb, lc, gs, ms, h))"
  let _ = lemma(
    "sl_return_g",
    "\{env}∀ ls : List[\{sa}], \{triple_g(ret_pre, "[Return]", sa_false, "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([sl_triple_g, @lists.map()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths([keep] + lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safer")])),
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.disj1_tac,
      @tactics.exists_tac(tm("(vb : List[Value])")),
      @tactics.exists_tac(tm("LBase((vs0 : List[Value]), NIL)")),
      @simp.asm_rewrite_tac(
        ths([
          @wasm.thm("lfill"),
          keep,
          thm("lift"),
          @lists.map_append(),
          @equal.gsym(@lists.append_assoc()),
          @lists.append_nil(),
        ]),
      ),
      @tactics.exists_tac(tm("(j : Num)")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
}

///|
/// The facts keep adds to an assertion: the store's functions and the
/// frame's instance (named, so that substituting does not rewrite fs and
/// inst away).
fn define_in_mod() -> Unit raise {
  def(
    "in_mod", "in_mod((fs : List[Cl]), (inst : Inst), (s : Wstore), (f : Wframe)) == (s_funcs(s) == fs && f_inst(f) == inst)",
  )
  let _ = lemma(
    "keep_in_mod",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ q : \{assn}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], keep(fs, inst, q, s, f, vs) == (in_mod(fs, inst, s, f) && q(s, f, vs))",
    @simp.rewrite_tac(ths([thm("keep"), thm("in_mod"), @theorems.conj_assoc()])),
  )
}

///|
/// The facts of a g triple's precondition, as assumptions: specs_ok,
/// in_mod, and the lift written out.
fn g_pre_facts() -> @tactics.Tactic {
  let rws = [thm("keep_in_mod")] + lift_facts()
  @tactics.disch_then(th => {
    @tactics.strip_assume_tac(@simp.rewrite_rule(ths(rws))(th))
  })
}

///|
/// Cases on the steps left, n, with the assumption specs_ok(n, ...)
/// following (struct_cases_tac rewrites only the goal).
fn cases_n_specs() -> @tactics.Tactic raise {
  seq([
    @tactics.first_x_assum(th => {
      if @basics.strip_comb(@kernel.concl(th)).0 is Const("specs_ok", _) {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
    @tactics.disch_tac,
  ])
}

///|
/// specs_ok(n', ...) from specs_ok(SUC(n'), ...).
fn specs_pred(n : String) -> @tactics.Tactic raise {
  have(
    "specs_ok((\{n} : Num), (G : \{specs_ty}), (fs : List[Cl]), (inst : Inst))",
    seq([
      @tactics.match_mp_tac(thm("specs_down")),
      @tactics.exists_tac(tm("SUC((\{n} : Num))")),
      @simp.asm_rewrite_tac(ths([arith("∀ n : Num, n <= SUC(n)")])),
    ]),
  )
}

///|
/// keep(fs, inst, lift(x, fr), s2, f2, ...) from keep(fs, inst, lift(y,
/// fr), s2, f2, v) in the assumptions: lift_mono, with y and v.
fn keep_lift_mono(y : String, v : String) -> @tactics.Tactic raise {
  seq([
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("keep_in_mod")]))),
    split_conjs(),
    @simp.asm_rewrite_tac(ths([thm("keep_in_mod")])),
    @tactics.match_mp_tac(thm("lift_mono")),
    @tactics.exists_tac(tm(y)),
    @tactics.exists_tac(tm(v)),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.meson_tac(ths([]))),
  ])
}

///|
/// br_if and if for g triples (as conditionals.mbt): the condition c on
/// top of vs0 steps once, to `zero` or `nonzero`.
fn prove_conditional_g(
  name : String,
  stmt : String,
  x : String,
  zero : String,
  nonzero : String,
  rule0 : @kernel.Thm,
  rule1 : @kernel.Thm,
  if_zero : @tactics.Tactic,
  if_nonzero : @tactics.Tactic,
  prefix_name : String,
) -> @kernel.Thm raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let c = "Basic(EConstNum(ConstInt32((c : \{w32}))))"
  let code = "[\{c}, \{x}]"
  let prefix = @bool.gen_all(thm(prefix_name))
  let cases = step_cases_of(s, f, code)
  let rb_lift = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()[0]
  let lfill = @wasm.thm("lfill")
  let vs0 = "(vs0 : List[Value])"
  let progress = (out : String, rule : @kernel.Thm) => {
    seq([
      @tactics.exists_tac(s),
      @tactics.exists_tac(f),
      @tactics.exists_tac(tm("APPEND(MAP(v_to_e, \{vs0}), \{out})")),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List([s, f, tm("LBase(\{vs0}, NIL)"), tm(code), s, f, tm(out)]),
          @wasm.thm("decomp_reduce"),
        ),
      ),
      @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @tactics.match_mp_tac(rb_lift),
      @tactics.match_mp_tac(rule),
      @simp.asm_rewrite_tac(ths([])),
    ])
  }
  let steps = (finish : @tactics.Tactic) => {
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => {
        @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))
      }),
      subst_vars(),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.append_nil()])),
      finish,
    ])
  }
  lemma(
    name,
    stmt,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_g"), @lists.map()])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.repeat_tac(@tactics.gen_tac),
      g_pre_facts(),
      subst_vars(),
      // p holds of vs0, below the condition
      have(
        "keep(fs, inst, lift((p : \{sassn}), (fr : \{hprop})), (s : Wstore), (f : Wframe), \{vs0})",
        seq([
          @simp.rewrite_tac(ths([thm("keep_in_mod"), thm("lift")])),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.exists_tac(tm("(j : Num)")),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
      @simp.rewrite_tac(
        ths([
          @lists.map_append(),
          @lists.map(),
          @wasm.thm("v_to_e"),
          @equal.gsym(@lists.append_assoc()),
          @lists.append(),
        ]),
      ),
      cases_n_specs(),
      @simp.rewrite_tac(ths([thm("safer")])),
      specs_pred("n'"),
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(c : \{w32}) == word(0)")),
        @list.List([
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([progress(zero, rule0), steps(if_zero)]),
          ),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([progress(nonzero, rule1), steps(if_nonzero)]),
          ),
        ]),
      ),
    ]),
  )
}

///|
fn prove_specs_rules() -> Unit raise {
  let sa = sassn
  let env = env_vars()
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(c))]) && p(vs0, lc, gs, ms, h))"
  let by_hypothesis = @meson.asm_meson_tac(ths([]))
  let _ = prove_conditional_g(
    "sl_br_if_g",
    "\{env}∀ p : \{sa}, ∀ q : \{sa}, ∀ ls : List[\{sa}], ∀ i : Num, ∀ c : \{w32}, (!(c == word(0)) → \{triple_g("p", "[Br(i)]", "q", "ls")}) && (c == word(0) → (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, p(vs, lc, gs, ms, h) → q(vs, lc, gs, ms, h))) → \{triple_g(pre, "[Br_if(i)]", "q", "ls")}",
    "Basic(Br_if((i : Num)))",
    "(NIL : List[Einstr])",
    "[Basic(Br((i : Num)))]",
    rs[30],
    rs[31],
    seq([
      @tactics.match_mp_tac(thm("safer_vals")),
      keep_lift_mono("(p : \{sa})", "(vs0 : List[Value])"),
    ]),
    by_hypothesis,
    "prefix_br_if",
  )
  let _ = prove_conditional_g(
    "sl_if_g",
    "\{env}∀ p : \{sa}, ∀ q : \{sa}, ∀ ls : List[\{sa}], ∀ tb : Tb, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ c : \{w32}, (!(c == word(0)) → \{triple_g("p", "[Block(tb, bs1)]", "q", "ls")}) && (c == word(0) → \{triple_g("p", "[Block(tb, bs2)]", "q", "ls")}) → \{triple_g(pre, "[If(tb, bs1, bs2)]", "q", "ls")}",
    "Basic(If((tb : Tb), (bs1 : List[B_e]), (bs2 : List[B_e])))",
    "[Basic(Block((tb : Tb), (bs2 : List[B_e])))]",
    "[Basic(Block((tb : Tb), (bs1 : List[B_e])))]",
    rs[25],
    rs[26],
    by_hypothesis,
    by_hypothesis,
    "prefix_if",
  )
  prove_block_g()
  prove_loop_g()
}

///|
/// The block rule for g triples (as sl_block).
fn prove_block_g() -> Unit raise {
  let sa = sassn
  let env = env_vars()
  let block = "Basic(Block(Tbv((ot : Option[Valtype])), (bs : List[B_e])))"
  let prefix = @bool.gen_all(thm("prefix_block"))
  let s_ = tm("(s : Wstore)")
  let f_ = tm("(f : Wframe)")
  let cases = step_cases_of(s_, f_, "[\{block}]")
  let lists = [@lists.map(), @lists.append(), @lists.append_nil()]
  let tb_tf_tbv = thm("tb_tf_tbv")
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == vs0 && pb(NIL, lc, gs, ms, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ r : List[Value], vs == APPEND(vs0, r) && (qb(r, lc, gs, ms, h) || lb(r, lc, gs, ms, h)))"
  let fr = "(fr : \{hprop})"
  let _ = lemma(
    "sl_block_g",
    "\{env}∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ pb : \{sa}, ∀ qb : \{sa}, ∀ lb : \{sa}, ∀ ls : List[\{sa}], ∀ vs0 : List[Value], (∀ r : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, lb(r, lc, gs, ms, h) → LENGTH(r) == LENGTH(tbv_results(ot))) && \{triple_g("pb", "bs", "qb", "CONS(lb, ls)")} → \{triple_g(pre, "[Block(Tbv(ot), bs)]", post, "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_g")])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.repeat_tac(@tactics.gen_tac),
      g_pre_facts(),
      subst_vars(),
      @simp.rewrite_tac(ths(lists)),
      cases_n_specs(),
      @simp.rewrite_tac(ths([thm("safer")])),
      specs_pred("n'"),
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          @meson.meson_tac(ths([thm("block_step")])),
          seq([
            @tactics.x_gen_tac(tm("(t1 : Wstore)")),
            @tactics.x_gen_tac(tm("(t2 : Wframe)")),
            @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
            @tactics.disch_tac,
            @tactics.first_x_assum(th => {
              @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))
            }),
            @tactics.first_x_assum(th => {
              @tactics.mp_tac(@drule.match_mp(cases)(th))
            }),
            @simp.rewrite_tac(
              ths([tb_tf_tbv, @ind_types.injectivity("tf")] + lists),
            ),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @tactics.match_mp_tac(thm("safer_label")),
            @tactics.exists_tac(tm("keep(fs, inst, lift((qb : \{sa}), \{fr}))")),
            @tactics.exists_tac(tm("keep(fs, inst, lift((lb : \{sa}), \{fr}))")),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                // the body is safe: its triple, from an empty stack
                seq([
                  @tactics.first_x_assum(th => {
                    @tactics.mp_tac(
                      @bool.ispecl(
                        @list.List([
                          tm("(n' : Num)"),
                          tm(fr),
                          s_,
                          f_,
                          tm("(NIL : List[Value])"),
                        ]),
                        th,
                      ),
                    )
                  }),
                  @simp.rewrite_tac(
                    ths(lists + [thm("keep_in_mod"), thm("lift")]),
                  ),
                  @meson.asm_meson_tac(ths([])),
                ]),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    seq([
                      @tactics.repeat_tac(@tactics.strip_tac),
                      keep_lift_mono("(qb : \{sa})", "(vs : List[Value])"),
                    ]),
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
                            @simp.rewrite_tac(
                              ths([thm("keep_in_mod"), thm("lift")]),
                            ),
                            @tactics.repeat_tac(@tactics.strip_tac),
                            @tactics.first_x_assum(th => {
                              @tactics.strip_assume_tac(
                                @drule.match_mp(thm("star_some"))(th),
                              )
                            }),
                            @meson.asm_meson_tac(ths([])),
                          ]),
                          seq([
                            @simp.rewrite_tac(
                              ths([
                                @lists.append_nil(),
                                @equal.gsym(@lists.map_append()),
                              ]),
                            ),
                            @tactics.match_mp_tac(thm("safer_vals")),
                            keep_lift_mono("(lb : \{sa})", "(vs : List[Value])"),
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

///|
/// The loop rule for g triples (as sl_loop).
fn prove_loop_g() -> Unit raise {
  let sa = sassn
  let env = env_vars()
  let loop_e = "Basic(Loop(Tbv((ot : Option[Valtype])), (bs : List[B_e])))"
  let prefix = @bool.gen_all(thm("prefix_loop"))
  let s_ = tm("(s : Wstore)")
  let f_ = tm("(f : Wframe)")
  let cases = step_cases_of(s_, f_, "[\{loop_e}]")
  let lists = [
    @lists.map(),
    @lists.append(),
    @lists.append_nil(),
    @lists.length(),
  ]
  let tb_tf_tbv = thm("tb_tf_tbv")
  let lb = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && linv(lc, gs, ms, h)"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == vs0 && linv(lc, gs, ms, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ r : List[Value], vs == APPEND(vs0, r) && qb(r, lc, gs, ms, h))"
  let fr = "(fr : \{hprop})"
  let pre_facts = [thm("keep_in_mod")] + lift_facts()
  let _ = lemma(
    "sl_loop_g",
    "\{env}∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ linv : (List[Value], List[Value], Num, \{heap}) -> Bool, ∀ qb : \{sa}, ∀ ls : List[\{sa}], ∀ vs0 : List[Value], \{triple_g(lb, "bs", "qb", "CONS(\{lb}, ls)")} → \{triple_g(pre, "[Loop(Tbv(ot), bs)]", post, "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple_g")])),
      @tactics.disch_tac,
      @tactics.gen_tac,
      @tactics.x_gen_tac(tm(fr)),
      @tactics.repeat_tac(@tactics.gen_tac),
      // by induction on the steps left, for every state and stack
      @tactics.spec_tac(tm("(vs : List[Value])"), tm("(vs : List[Value])")),
      @tactics.spec_tac(f_, f_),
      @tactics.spec_tac(s_, s_),
      @tactics.spec_tac(tm("(n : Num)"), tm("(n : Num)")),
      @tactics.thenl(
        @nums.induct_tac,
        @list.List([
          @simp.rewrite_tac(ths([thm("safer")])),
          seq([
            @tactics.repeat_tac(@tactics.gen_tac),
            g_pre_facts(),
            subst_vars(),
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths(lists))),
            @simp.rewrite_tac(ths(lists)),
            @simp.rewrite_tac(ths([thm("safer")])),
            specs_pred("n"),
            @tactics.disj2_tac,
            @tactics.disj2_tac,
            @tactics.disj2_tac,
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                @meson.meson_tac(ths([thm("loop_step")])),
                seq([
                  @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                  @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                  @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                  @tactics.disch_tac,
                  @tactics.first_x_assum(th => {
                    @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))
                  }),
                  @tactics.first_x_assum(th => {
                    @tactics.mp_tac(@drule.match_mp(cases)(th))
                  }),
                  @simp.rewrite_tac(
                    ths([tb_tf_tbv, @ind_types.injectivity("tf")] + lists),
                  ),
                  @tactics.repeat_tac(@tactics.strip_tac),
                  subst_vars(),
                  @simp.rewrite_tac(ths(lists)),
                  @tactics.match_mp_tac(thm("safer_label")),
                  @tactics.exists_tac(
                    tm("keep(fs, inst, lift((qb : \{sa}), \{fr}))"),
                  ),
                  @tactics.exists_tac(tm("keep(fs, inst, lift(\{lb}, \{fr}))")),
                  @tactics.thenl(
                    @tactics.conj_tac,
                    @list.List([
                      // the body is safe from the invariant
                      seq([
                        @tactics.first_x_assum(th => {
                          @tactics.mp_tac(
                            @bool.ispecl(
                              @list.List([
                                tm("(n : Num)"),
                                tm(fr),
                                s_,
                                f_,
                                tm("(NIL : List[Value])"),
                              ]),
                              th,
                            ),
                          )
                        }),
                        @simp.rewrite_tac(ths(lists + pre_facts)),
                        @meson.asm_meson_tac(ths([])),
                      ]),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          // the body's values leave the loop
                          seq([
                            @tactics.repeat_tac(@tactics.strip_tac),
                            keep_lift_mono("(qb : \{sa})", "(vs : List[Value])"),
                          ]),
                          // a br 0 runs the loop again, from the invariant
                          seq([
                            @tactics.repeat_tac(@tactics.gen_tac),
                            @tactics.disch_tac,
                            @tactics.disch_then(th => @tactics.mp_tac(th)),
                            @simp.rewrite_tac(ths(pre_facts)),
                            @tactics.repeat_tac(@tactics.strip_tac),
                            subst_vars(),
                            @simp.rewrite_tac(ths(lists)),
                            @tactics.match_mp_tac(thm("safer_down")),
                            @tactics.exists_tac(tm("(n : Num)")),
                            @simp.asm_rewrite_tac(ths([])),
                            @tactics.first_x_assum(th => {
                              @tactics.match_mp_tac(th)
                            }),
                            @simp.rewrite_tac(ths(pre_facts)),
                            @meson.asm_meson_tac(ths([])),
                          ]),
                        ]),
                      ),
                    ]),
                  ),
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
/// The rules for calls: a call of a function with a spec in G
/// (sl_call_g), and G's specs from their bodies (sl_funs_g, which may
/// assume G's specs: recursion).
fn prove_call_g() -> Unit raise {
  let sa = sassn
  let env = env_vars()
  let lists = [@lists.map(), @lists.append(), @lists.append_nil()]
  let specs_assum = (ttac : (@kernel.Thm) -> @tactics.Tactic) => {
    @tactics.first_x_assum(th => {
      if @basics.strip_comb(@kernel.concl(th)).0 is Const("specs_ok", _) {
        ttac(th)
      } else {
        @tactics.no_tac
      }
    })
  }
  let _ = lemma(
    "sl_call_g",
    "\{env}∀ j : Num, ∀ P : \{fprop}, ∀ Q : \{fprop}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], ∀ ls : List[\{sa}], G(sfunc_ind(inst, j), P, Q) → \{triple_g(call_pre("P", "vs0", "lc0"), "[Call(j)]", call_post("Q", "vs0", "lc0"), "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @simp.rewrite_tac(ths([thm("sl_triple_g"), @lists.map()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      cases_n_specs(),
      @simp.rewrite_tac(ths([thm("safer")])),
      have(
        "f_inst((f : Wframe)) == (inst : Inst)",
        seq([
          @tactics.first_assum(th => {
            if @basics.strip_comb(@kernel.concl(th)).0 is Const("keep", _) {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          @simp.rewrite_tac(ths([thm("keep_in_mod"), thm("in_mod")])),
          @meson.meson_tac(ths([])),
        ]),
      ),
      safer_steps(
        seq([
          @tactics.exists_tac(tm("(s : Wstore)")),
          @tactics.exists_tac(tm("(f : Wframe)")),
          @tactics.exists_tac(
            tm(
              "APPEND(MAP(v_to_e, (vs : List[Value])), [Invoke(sfunc_ind(f_inst((f : Wframe)), (j : Num)))])",
            ),
          ),
          @tactics.match_accept_tac(thm("call_can_step")),
        ]),
        seq([
          @tactics.first_x_assum(th => {
            @tactics.strip_assume_tac(@drule.match_mp(thm("call_step"))(th))
          }),
          subst_only("s2"),
          subst_only("f2"),
          subst_only("es2"),
          @simp.asm_rewrite_tac(ths([])),
          specs_assum(th => @tactics.mp_tac(th)),
          @simp.rewrite_tac(ths([thm("specs_ok"), thm("inv_ok")])),
          @tactics.disch_then(th => {
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([
                  tm("sfunc_ind((inst : Inst), (j : Num))"),
                  tm("(P : \{fprop})"),
                  tm("(Q : \{fprop})"),
                ]),
                th,
              ),
            )
          }),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.disch_then(th => @tactics.match_mp_tac(th)),
          @simp.asm_rewrite_tac(ths([arith("∀ n : Num, n <= SUC(n)")])),
        ]),
      ),
    ]),
  )
  let pb = body_pre("P", "args", "zs")
  let qb = body_post("Q")
  let native = "EL(a, fs) == Func_native(inst, Tf(t1s, t2s), ts, es) && n_zeros(ts) == SOME(zs) && (∀ args : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, P(args, gs, ms, h) → LENGTH(args) == LENGTH(t1s)) && (∀ res : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, Q(res, gs, ms, h) → LENGTH(res) == LENGTH(t2s)) && (∀ args : List[Value], sl_triple_g(G, fs, inst, \{qb}, \{pb}, es, \{qb}, [\{qb}]))"
  let fr = "(fr : \{hprop})"
  let callee = "Wframe(APPEND((args : List[Value]), (zs : List[Value])), (inst : Inst))"
  let frame_code = "APPEND(MAP(v_to_e, (vs0 : List[Value])), [Frame(LENGTH((t2s : List[Valtype])), \{callee}, [Label(LENGTH(t2s), NIL, MAP(Basic, (es : List[B_e])))])])"
  let qin = "keep(fs, inst, lift(\{qb}, \{fr}))"
  let frame_facts = [
    @wasm.thm("f_inst"),
    @wasm.thm("f_locs"),
    thm("gvals"),
    thm("globs_ok"),
  ]
  let pre_facts = [thm("keep_in_mod"), thm("in_mod")] + lift_facts()
  // the body's results have the function's arity (from keep(..., vs) in
  // the goal's antecedent)
  let arity = seq([
    @simp.rewrite_tac(ths(pre_facts)),
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.first_x_assum(th => {
      @tactics.strip_assume_tac(@drule.match_mp(thm("star_some"))(th))
    }),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @meson.asm_meson_tac(ths([])),
  ])
  // the body's results, in the caller's frame, are the call's
  let results = seq([
    @simp.rewrite_tac(ths(pre_facts + [thm("gvals"), thm("globs_ok")])),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    rw_inst("f3"),
    @simp.asm_rewrite_tac(ths([])),
    @meson.asm_meson_tac(ths([])),
  ])
  let gen3 = seq([
    @tactics.x_gen_tac(tm("(s3 : Wstore)")),
    @tactics.x_gen_tac(tm("(f3 : Wframe)")),
    @tactics.x_gen_tac(tm("(vs3 : List[Value])")),
  ])
  let _ = lemma(
    "sl_funs_g",
    "∀ G : \{specs_ty}, ∀ fs : List[Cl], ∀ inst : Inst, (∀ a : Num, ∀ P : \{fprop}, ∀ Q : \{fprop}, G(a, P, Q) → (∃ t1s : List[Valtype], ∃ t2s : List[Valtype], ∃ ts : List[Valtype], ∃ es : List[B_e], ∃ zs : List[Value], \{native})) → (∀ n : Num, specs_ok(n, G, fs, inst))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.thenl(
        @nums.induct_tac,
        @list.List([
          seq([
            @simp.rewrite_tac(
              ths([thm("specs_ok"), thm("inv_ok"), @arith.le()]),
            ),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([thm("safer")])),
          ]),
          seq([
            @simp.rewrite_tac(ths([thm("specs_ok"), thm("inv_ok")])),
            @tactics.x_gen_tac(tm("(a : Num)")),
            @tactics.x_gen_tac(tm("(P : \{fprop})")),
            @tactics.x_gen_tac(tm("(Q : \{fprop})")),
            @tactics.disch_tac,
            @tactics.first_assum(h => {
              @tactics.first_assum(gm => @tactics.mp_tac(@drule.match_mp(h)(gm)))
            }),
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            @tactics.x_gen_tac(tm("(m : Num)")),
            @tactics.x_gen_tac(tm(fr)),
            @tactics.x_gen_tac(tm("(s : Wstore)")),
            @tactics.x_gen_tac(tm("(f : Wframe)")),
            @tactics.x_gen_tac(tm("(stk : List[Value])")),
            @tactics.x_gen_tac(tm("(vs0 : List[Value])")),
            @tactics.x_gen_tac(tm("(lc0 : List[Value])")),
            @tactics.x_gen_tac(tm("(l : List[\{assn}])")),
            @tactics.x_gen_tac(tm("(rq : \{assn})")),
            @tactics.disch_then(
              @tactics.conjuncts_then2(c => @tactics.assume_tac(c), c => {
                @tactics.strip_assume_tac(@simp.rewrite_rule(ths(pre_facts))(c))
              }),
            ),
            subst_only("stk"),
            have(
              "LENGTH((args : List[Value])) == LENGTH((t1s : List[Valtype]))",
              seq([
                @tactics.first_assum(th => {
                  @tactics.mp_tac(@drule.match_mp(thm("star_some"))(th))
                }),
                @tactics.repeat_tac(@tactics.strip_tac),
                @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                @meson.asm_meson_tac(ths([])),
              ]),
            ),
            have(
              "EL((a : Num), s_funcs((s : Wstore))) == Func_native((inst : Inst), Tf((t1s : List[Valtype]), (t2s : List[Valtype])), (ts : List[Valtype]), (es : List[B_e]))",
              @simp.asm_rewrite_tac(ths([])),
            ),
            // cases on m, with m <= SUC(n)
            @tactics.undisch_tac(tm("(m : Num) <= SUC((n : Num))")),
            @tactics.struct_cases_tac(
              @bool.spec(tm("(m : Num)"), @nums.num_cases()),
            ),
            @simp.rewrite_tac(ths([thm("safer"), @arith.le_suc()])),
            @tactics.disch_tac,
            have(
              "specs_ok((n' : Num), (G : \{specs_ty}), (fs : List[Cl]), (inst : Inst))",
              seq([
                @tactics.match_mp_tac(thm("specs_down")),
                @tactics.exists_tac(tm("(n : Num)")),
                @simp.asm_rewrite_tac(ths([])),
              ]),
            ),
            safer_steps(
              seq([
                @tactics.exists_tac(tm("(s : Wstore)")),
                @tactics.exists_tac(tm("(f : Wframe)")),
                @tactics.exists_tac(tm(frame_code)),
                @tactics.match_mp_tac(thm("invoke_can_step")),
                @tactics.exists_tac(tm("(t1s : List[Valtype])")),
                @tactics.exists_tac(tm("(ts : List[Valtype])")),
                @simp.asm_rewrite_tac(ths([])),
              ]),
              seq([
                forward2_3(thm("invoke_step")),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_only("s2"),
                subst_only("f2"),
                subst_only("es2"),
                // the caller's facts with its instance written inst
                @tactics.rule_assum_tac(
                  @simp.rewrite_rule(ths([thm("gvals"), thm("globs_ok")])),
                ),
                rw_inst("f"),
                @tactics.match_mp_tac(thm("frame_safe_r")),
                @tactics.exists_tac(tm(qin)),
                @tactics.exists_tac(tm(qin)),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    // the frame's content: the body's triple, in the callee's frame
                    seq([
                      @tactics.match_mp_tac(thm("safer_label_top")),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          seq([
                            @tactics.first_x_assum(body => {
                              if @basics.is_forall(@kernel.concl(body)) &&
                                show(@kernel.concl(body)).contains(
                                  "sl_triple_g",
                                ) {
                                @tactics.mp_tac(
                                  @bool.ispec(tm("(args : List[Value])"), body),
                                )
                              } else {
                                @tactics.no_tac
                              }
                            }),
                            @simp.rewrite_tac(ths([thm("sl_triple_g")])),
                            @tactics.disch_then(th => {
                              @tactics.mp_tac(
                                @bool.ispecl(
                                  @list.List([
                                    tm("(n' : Num)"),
                                    tm(fr),
                                    tm("(s : Wstore)"),
                                    tm(callee),
                                    tm("(NIL : List[Value])"),
                                  ]),
                                  th,
                                ),
                              )
                            }),
                            @simp.rewrite_tac(
                              ths(pre_facts + frame_facts + lists),
                            ),
                            @tactics.ants_tac,
                            @meson.asm_meson_tac(ths([])),
                            @tactics.disch_then(th => @tactics.accept_tac(th)),
                          ]),
                          seq([gen3, arity]),
                        ]),
                      ),
                    ]),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([gen3, results]),
                        seq([
                          gen3,
                          @tactics.disch_tac,
                          @tactics.thenl(
                            @tactics.conj_tac,
                            @list.List([
                              seq([
                                @tactics.first_x_assum(th => @tactics.mp_tac(th)),
                                arity,
                              ]),
                              seq([
                                @tactics.first_x_assum(th => @tactics.mp_tac(th)),
                                results,
                              ]),
                            ]),
                          ),
                        ]),
                      ]),
                    ),
                  ]),
                ),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  // a step of call-free code, then more code
  let cons_append = @equal.gsym(
    @simp.rewrite_conv(ths([@lists.append()]))(
      tm("APPEND([(i : B_e)], (rest : List[B_e]))"),
    ),
  )
  let _ = lemma(
    "sl_step_g",
    "\{env}∀ p : \{sa}, ∀ i : B_e, ∀ q : \{sa}, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], sl_triple(p, [i], q) → call_free_b([i]) → \{triple_g("q", "rest", "r", "ls")} → \{triple_g("p", "CONS(i, rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.subst1_tac(cons_append),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(tm("(q : \{sa})")),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(thm("sl_triple_g_of")),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(thm("sl_triple_l_of")),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ]),
  )
}

///|
/// The rules sym_tac uses on g triples: the derived ones (sym.mbt), and
/// the steps for call and return on exact states.
fn prove_sym_g() -> Unit raise {
  prove_sym_derived(true)
  let sa = sassn
  let env = env_vars()
  let st = thm("st")
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([st])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let cons_append = (i : String) => {
    @equal.gsym(
      @simp.rewrite_conv(ths([@lists.append()]))(
        tm("APPEND([\{i}], (rest : List[B_e]))"),
      ),
    )
  }
  let q = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == aout && Rout(gs, ms, h)"
  let after = "st(APPEND(v0, aout), l, Rout)"
  let _ = lemma(
    "sl_call_st_g",
    "\{env}∀ j : Num, ∀ P : \{fprop}, ∀ aout : List[Value], ∀ Rout : \{rty}, ∀ v0 : List[Value], ∀ ain : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], G(sfunc_ind(inst, j), P, \{q}) → (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → P(ain, gs, ms, h)) && \{triple_g(after, "rest", "r", "ls")} → \{triple_g("st(APPEND(v0, ain), l, R)", "CONS(Call(j), rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.subst1_tac(cons_append("Call((j : Num))")),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(tm(after)),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(tm(call_pre("P", "v0", "l"))),
      @tactics.exists_tac(tm(call_post("(\{q})", "v0", "l"))),
      @tactics.exists_tac(tm("(ls : List[\{sa}])")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.match_mp_tac(thm("sl_call_g")),
              @tactics.first_assum(th => @tactics.accept_tac(th)),
            ]),
          ),
          solve(simple),
        ]),
      ),
    ]),
  )
  let ret_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ vb : List[Value], vs == APPEND(vs0, vb) && rp(vb, lc, gs, ms, h))"
  let _ = lemma(
    "sl_return_st_g",
    "\{env}∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ rest : List[B_e], ∀ r : \{sa}, ∀ ls : List[\{sa}], (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → (∃ vs0 : List[Value], ∃ vb : List[Value], v == APPEND(vs0, vb) && rp(vb, l, gs, ms, h))) → \{triple_g("st(v, l, R)", "CONS(Return, rest)", "r", "ls")}",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.subst1_tac(cons_append("Return")),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(tm(sa_false)),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.match_mp_tac(thm("sl_conseq_g")),
            @tactics.exists_tac(tm(ret_pre)),
            @tactics.exists_tac(tm(sa_false)),
            @tactics.exists_tac(tm("(ls : List[\{sa}])")),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(
              @list.List([
                solve(@tactics.match_accept_tac(thm("sl_return_g"))),
                solve(simple),
              ]),
            ),
          ]),
          @tactics.match_accept_tac(thm("sl_false_g")),
        ]),
      ),
    ]),
  )
}
