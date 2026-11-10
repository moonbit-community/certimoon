// example_fact: a recursive function with an early return. Function 0 of
// the module is factorial on i32 (modulo 2^32):
//
//   (func $fact (param i32) (result i32)
//     local.get 0
//     i32.eqz
//     if
//       i32.const 1
//       return
//     end
//     local.get 0
//     local.get 0
//     i32.const 1
//     i32.sub
//     call $fact
//     i32.mul)
//
// Its spec (fact_spec) is: from the argument x, the result fact_w(val(x)),
// with any R on the globals, the memory's length and the heap kept. The
// body is proved by sym_prove as a g triple, the recursive call by that
// same spec (fact_call), the return by the return assertion; sl_funs_g
// then proves the spec for every number of steps (fact_specs), and
// example_fact is the call `call 0` as a module triple.

///|
fn prove_example_fact() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  def(
    "fact_w",
    "fact_w(0) == (word(1) : \{w}) && fact_w(SUC(n)) == word_mul(word(SUC(n)), fact_w(n))",
  )
  let fact_w = thm("fact_w")
  let fact_suc = lemma(
    "fact_w_suc",
    "∀ x : \{w}, ∀ k : Num, val(x) == SUC(k) → word_mul(x, fact_w(k)) == fact_w(val(x))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(word(SUC((k : Num))) : \{w}) == (x : \{w})",
        seq([
          @tactics.first_x_assum(th => @simp.rewrite_tac(ths([@equal.gsym(th)]))),
          @simp.rewrite_tac(ths([@words.word_val()])),
        ]),
      ),
      @simp.asm_rewrite_tac(ths([fact_w])),
    ]),
  )
  let fact_step = lemma(
    "fact_w_step",
    "∀ x : \{w}, !(x == word(0)) → word_mul(x, fact_w(val(word_sub(x, word(1))))) == fact_w(val(x))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([@equal.gsym(@words.val_eq_0())])),
      ),
      have("1 <= val((x : \{w}))", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(
        ths([@words.val_word_sub_cases(), @words.val_word_1()]),
      ),
      @tactics.match_mp_tac(fact_suc),
      @int.asm_arith_tac,
    ]),
  )
  let pl = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [\{i("(x : \{w})")}] && (R : \{rty})(gs, ms, h)"
  let ql = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [\{i("fact_w(val((x : \{w})))")}] && (R : \{rty})(gs, ms, h)"
  def(
    "fact_spec",
    "fact_spec((inst : Inst), (a : Num), (P : \{fprop}), (Q : \{fprop})) == (a == sfunc_ind(inst, 0) && (∃ x : \{w}, ∃ R : \{rty}, P == (\{pl}) && Q == (\{ql})))",
  )
  let spec_call = lemma(
    "fact_call",
    "∀ inst : Inst, ∀ x : \{w}, ∀ R : \{rty}, fact_spec(inst, sfunc_ind(inst, 0), \{pl}, \{ql})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("fact_spec")])),
      @tactics.exists_tac(tm("(x : \{w})")),
      @tactics.exists_tac(tm("(R : \{rty})")),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let body = "[Local_get(0), Testop(T_i32, Eqz), If(Tbv(NONE), [EConstNum(ConstInt32(word(1))), Return], NIL), Local_get(0), Local_get(0), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Sub)), Call(0), Binop(T_i32, Binop_i(Mul))]"
  let qb = body_post("(\{ql})")
  let pb = body_pre("(\{pl})", "args", "NIL")
  let after_if = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == [\{i("x")}] && !(x == word(0)) && R(gs, ms, h)"
  let body_th = sym_prove(
    "fact_body",
    "∀ fs : List[Cl], ∀ inst : Inst, ∀ x : \{w}, ∀ R : \{rty}, ∀ args : List[Value], sl_triple_g(fact_spec(inst), fs, inst, \{qb}, \{pb}, \{body}, \{qb}, [\{qb}])",
    [],
    [
      // the return: 1 is fact_w(val(0))
      seq([
        @tactics.exists_tac(tm("(NIL : List[Value])")),
        @simp.rewrite_tac(ths([@lists.append()])),
      ]),
      // after the call: x * fact_w(val(x) - 1) is fact_w(val(x))
      seq([
        @tactics.match_mp_tac(fact_step),
        @tactics.first_assum(th => @tactics.accept_tac(th)),
      ]),
    ],
    afters=[after_if],
    specs=[spec_call],
    rws=[fact_w, @words.val_word_0()],
    kind="lemma",
  )
  let tf = "Tf([T_num(T_i32)], [T_num(T_i32)])"
  let native = "EL(sfunc_ind(inst, 0), fs) == Func_native(inst, \{tf}, NIL, \{body})"
  let specs = lemma(
    "fact_specs",
    "∀ fs : List[Cl], ∀ inst : Inst, \{native} → (∀ n : Num, specs_ok(n, fact_spec(inst), fs, inst))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_funs_g")),
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("fact_spec")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.exists_tac(tm("[T_num(T_i32)]")),
      @tactics.exists_tac(tm("[T_num(T_i32)]")),
      @tactics.exists_tac(tm("(NIL : List[Valtype])")),
      @tactics.exists_tac(tm(body)),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@tactics.first_assum(th => @tactics.accept_tac(th))),
          // the body, by its sym_prove proof
          solve(
            seq([
              @tactics.x_gen_tac(tm("(args : List[Value])")),
              @tactics.accept_tac(
                @bool.ispecl(
                  @list.List(
                    [
                      "(fs : List[Cl])",
                      "(inst : Inst)",
                      "(x : \{w})",
                      "(R : \{rty})",
                      "(args : List[Value])",
                    ].map(tm),
                  ),
                  body_th,
                ),
              ),
            ]),
          ),
          solve(
            @simp.rewrite_tac(
              ths([@wasm.thm("n_zeros"), @lists.map(), @wasm.thm("those")]),
            ),
          ),
          solve(
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              @simp.rewrite_tac(ths([])),
              @tactics.repeat_tac(@tactics.strip_tac),
              @simp.asm_rewrite_tac(ths([@lists.length()])),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == APPEND(vs0, [\{i("x")}]) && lc == lc0 && R(gs, ms, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == APPEND(vs0, [\{i("fact_w(val(x))")}]) && lc == lc0 && R(gs, ms, h)"
  let simple = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let th = @tactics.prove(
    tm(
      "∀ fs : List[Cl], ∀ inst : Inst, ∀ x : \{w}, ∀ R : \{rty}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], \{native} → sl_triple_m(fs, inst, \{pre}, [Call(0)], \{post}, NIL)",
    ),
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
      @tactics.exists_tac(tm("fact_spec((inst : Inst))")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.match_mp_tac(specs),
            @tactics.first_assum(th => @tactics.accept_tac(th)),
          ]),
          seq([
            @tactics.match_mp_tac(thm("sl_conseq_g")),
            @tactics.exists_tac(tm(call_pre("(\{pl})", "vs0", "lc0"))),
            @tactics.exists_tac(tm(call_post("(\{ql})", "vs0", "lc0"))),
            @tactics.exists_tac(tm("(NIL : List[\{sassn}])")),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(
              @list.List([
                solve(
                  seq([
                    @tactics.match_mp_tac(thm("sl_call_g")),
                    @tactics.match_accept_tac(spec_call),
                  ]),
                ),
                solve(simple),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  record("example_fact", th, kind="example")
  prove_fact_closed(th, native)
}

///|
/// fact_closed: example_fact about runs, with no assertion left. In a
/// store whose function 0 is factorial, a frame of the instance with a
/// memory j, every run of `call 0` with x on the stack either can step
/// again or has ended with fact_w(val(x)) on the stack, the store's
/// functions, the frame's instance and locals, the globals and the
/// memory's bytes as they were. From sl_triple_m_adequate_whole, with
/// example_fact's R saying the globals and the memory are exactly the
/// starting ones.
fn prove_fact_closed(example : @kernel.Thm, native : String) -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let exact = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => gs == gvals((s : Wstore), (f : Wframe)) && ms == mem_length(EL((j : Num), s_mems(s))) && h == heap_of(EL(j, s_mems(s)))"
  let triple = @bool.ispecl(
    @list.List(
      ["(fs : List[Cl])", "(inst : Inst)", "(x : \{w})", exact, "(vs0 : List[Value])", "f_locs((f : Wframe))"].map(tm),
    ),
    example,
  )
  // with R applied, so that the assumption and the goal agree
  let triple = @equal.conv_rule(@equal.try_conv(@equal.redepth_conv(@equal.beta_conv)), triple)
  // the triple's precondition and postcondition, as instantiated
  let args = @basics.strip_comb(@basics.dest_imp(@kernel.concl(triple)).1).1.to_array()
  let adequate = @bool.ispecl(
    @list.List(
      [
        tm("(fs : List[Cl])"),
        tm("(inst : Inst)"),
        args[2],
        tm("[Call(0)]"),
        args[4],
        tm("(j : Num)"),
        tm("(s : Wstore)"),
        tm("(f : Wframe)"),
        tm("APPEND((vs0 : List[Value]), [\{i("(x : \{w})")}])"),
        tm("(s2 : Wstore)"),
        tm("(f2 : Wframe)"),
        tm("(es2 : List[Einstr])"),
      ],
    ),
    thm("sl_triple_m_adequate_whole"),
  )
  let th = @tactics.prove(
    tm(
      "∀ fs : List[Cl], ∀ inst : Inst, ∀ s : Wstore, ∀ f : Wframe, ∀ j : Num, ∀ x : \{w}, ∀ vs0 : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], \{native} && s_funcs(s) == fs && f_inst(f) == inst && smem_ind(inst) == SOME(j) && j < LENGTH(s_mems(s)) && globs_ok(s, f) && reduce_trans((s, f, APPEND(MAP(v_to_e, APPEND(vs0, [\{i("x")}])), [Basic(Call(0))])), (s2, f2, es2)) → (es2 == MAP(v_to_e, APPEND(vs0, [\{i("fact_w(val(x))")}])) && s_funcs(s2) == fs && f_inst(f2) == inst && f_locs(f2) == f_locs(f) && gvals(s2, f2) == gvals(s, f) && heap_of(EL(j, s_mems(s2))) == heap_of(EL(j, s_mems(s)))) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    ),
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(triple),
      @tactics.thenl(
        @tactics.ants_tac,
        @list.List([@simp.asm_rewrite_tac(ths([])), @tactics.disch_tac]),
      ),
      @tactics.mp_tac(adequate),
      @simp.asm_rewrite_tac(ths([@lists.map()])),
      @meson.meson_tac(ths([])),
    ]),
  )
  record("fact_closed", th, kind="theorem")
}
