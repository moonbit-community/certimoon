// example_call: a call. Function 0 of the module doubles its i32
// argument:
//
//   (func (param i32) (result i32) local.get 0 local.get 0 i32.add)
//
// and `call 0` with x on the stack leaves x + x there, the caller's locals
// and the rest of its stack as they were. The body is proved with
// sym_prove (double_body), made a module triple (sl_triple_m_of: it has no
// calls), and given to sl_call with the spec "the argument is x, the
// result x + x".

///|
fn prove_example_call() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let sa = sassn
  let body = program("double_code", "[Local_get(0), Local_get(0), Binop(T_i32, Binop_i(Add))]")
  let x = "(x : \{w})"
  let r = "(R : \{rty})"
  let sum = i("word_add(\{x}, \{x})")
  let body_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == [\{i(x)}] && \{r}(gs, ms, h)"
  let body_post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{sum}] && \{r}(gs, ms, h)"
  let double = sym_prove(
    "double_body",
    "∀ x : \{w}, ∀ R : \{rty}, sl_triple(\{body_pre}, \{body}, \{body_post})",
    [],
    [],
    kind="lemma",
  )
  // the function's spec, for this x
  let p = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [\{i(x)}] && \{r}(gs, ms, h)"
  let q = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [\{sum}] && \{r}(gs, ms, h)"
  let fs = "(fs : List[Cl])"
  let tabs = "(tabs : List[(Tab_t, List[V_ref])])"
  let inst = "(inst : Inst)"
  let vs0 = "(vs0 : List[Value])"
  let lc0 = "(lc0 : List[Value])"
  let i32 = "[T_num(T_i32)]"
  let call = @equal.beta_rule(
    @bool.ispecl(
      @list.List(
        [fs, tabs, inst, "0", i32, i32, "(NIL : List[Valtype])", body, "(NIL : List[Value])", p, q, vs0, lc0, "(NIL : List[\{sa}])"].map(tm),
      ),
      thm("sl_call"),
    ),
  )
  let call_free_body = @tactics.prove(
    tm("call_free_b(\{body})"),
    seq([
      @simp.pure_rewrite_tac(ths(programs)),
      @simp.rewrite_tac(ths([thm("call_free_b"), @lists.all()])),
      @tactics.conv_tac(@equal.top_depth_conv(has_call_conv())),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let ent = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([@lists.append(), @lists.append_nil(), @lists.length()])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let native = "EL(sfunc_ind(\{inst}, 0), \{fs}) == Func_native(\{inst}, Tf(\{i32}, \{i32}), NIL, \{body})"
  let th = @tactics.prove(
    tm(
      "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ x : \{w}, ∀ R : \{rty}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], \{native} → sl_triple_m(fs, tabs, inst, (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == APPEND(vs0, [\{i("x")}]) && lc == lc0 && R(gs, ms, h), [Call(0)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == APPEND(vs0, [\{i("word_add(x, x)")}]) && lc == lc0 && R(gs, ms, h), NIL)",
    ),
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(triple_m_pre(@kernel.concl(call))),
      @tactics.exists_tac(triple_m_post(@kernel.concl(call))),
      @tactics.thenl(
        @tactics.repeat_tac(@tactics.conj_tac),
        @list.List([
          // the caller's state gives the function its argument
          seq([ent, @tactics.exists_tac(tm("[\{i(x)}]")), @simp.asm_rewrite_tac(ths([@lists.length()]))]),
          // the call
          seq([
            @tactics.match_mp_tac(call),
            @simp.asm_rewrite_tac(ths([@wasm.thm("n_zeros"), @lists.map(), @wasm.thm("those"), @lists.length()])),
            @tactics.repeat_tac(@tactics.strip_tac),
            // the body, from its sym_prove proof
            @tactics.first(@list.List([
              solve(seq([
                @tactics.match_mp_tac(thm("sl_conseq_m")),
                @tactics.exists_tac(tm(body_pre)),
                @tactics.exists_tac(tm(body_post)),
                @tactics.thenl(
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @list.List([
                    ent,
                    seq([
                      @tactics.match_mp_tac(thm("sl_triple_m_of")),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          @tactics.accept_tac(call_free_body),
                          seq([@tactics.match_mp_tac(thm("sl_triple_l_of")), @tactics.match_accept_tac(double)]),
                        ]),
                      ),
                    ]),
                    ent,
                  ]),
                ),
              ])),
              solve(ent),
            ])),
          ]),
          // the result is the caller's
          ent,
        ]),
      ),
    ]),
  )
  record("example_call", th, kind="example")
}

///|
/// The precondition of the triple at the end of an implication's chain.
fn triple_m_pre(t : @kernel.Term) -> @kernel.Term raise {
  triple_m_parts(t).0
}

///|
fn triple_m_post(t : @kernel.Term) -> @kernel.Term raise {
  triple_m_parts(t).1
}

///|
fn triple_m_parts(t : @kernel.Term) -> (@kernel.Term, @kernel.Term) raise {
  let mut c = t
  while @basics.is_imp(c) {
    c = @basics.dest_imp(c).1
  }
  guard args_of(c, "sl_triple_m", 7) is Some(args) else {
    raise Failure("certimoon/logic: not a module triple: " + show(c))
  }
  (args[3], args[5])
}
