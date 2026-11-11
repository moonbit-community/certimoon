// example_indirect: a call through a function table. apply_code takes x
// and k in its locals and calls, on x, the function that table 0 of the
// instance holds at index k, if its type is the instance's type 0:
//
//   local.get 0
//   local.get 1
//   call_indirect 0 (type 0)
//
// The triple names the store's tables, tabs; its hypotheses say that
// table 0 holds the function a at k, that a's type is type 0, and that a
// is double_code (example_call). Then apply leaves x + x on the stack. a's
// spec (double_spec) is proved from its body by sl_funs_g, apply's body by
// sym_prove, which runs call_indirect by sl_call_indirect_st_g (the table's
// facts are left as its conditions, and the hypotheses prove them), and
// sl_triple_m_of_g drops the spec.

///|
fn prove_example_indirect() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let tabs_ty = "List[(Tab_t, List[V_ref])]"
  let pl = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [\{i("(x : \{w})")}] && (R : \{rty})(gs, ms, h)"
  let ql = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [\{i("word_add((x : \{w}), x)")}] && (R : \{rty})(gs, ms, h)"
  def(
    "double_spec",
    "double_spec((a : Num), (b : Num), (P : \{fprop}), (Q : \{fprop})) == (b == a && (∃ x : \{w}, ∃ R : \{rty}, P == (\{pl}) && Q == (\{ql})))",
  )
  let spec_call = lemma(
    "double_spec_holds",
    "∀ a : Num, ∀ x : \{w}, ∀ R : \{rty}, double_spec(a, a, \{pl}, \{ql})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("double_spec")])),
      @tactics.exists_tac(tm("(x : \{w})")),
      @tactics.exists_tac(tm("(R : \{rty})")),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  // double_code's body, as the function a of the spec
  let qb = body_post("(\{ql})")
  let pb = body_pre("(\{pl})", "args", "NIL")
  let double_th = sym_prove(
    "double_body_g",
    "∀ fs : List[Cl], ∀ tabs : \{tabs_ty}, ∀ inst : Inst, ∀ a : Num, ∀ x : \{w}, ∀ R : \{rty}, ∀ args : List[Value], sl_triple_g(double_spec(a), fs, tabs, inst, \{qb}, \{pb}, double_code, \{qb}, [\{qb}])",
    [],
    [],
    kind="lemma",
  )
  let tf = "Tf([T_num(T_i32)], [T_num(T_i32)])"
  let native = "EL(a, fs) == Func_native(inst, \{tf}, NIL, double_code)"
  let specs = lemma(
    "double_specs",
    "∀ fs : List[Cl], ∀ tabs : \{tabs_ty}, ∀ inst : Inst, ∀ a : Num, \{native} → (∀ n : Num, specs_ok(n, double_spec(a), fs, tabs, inst))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_funs_g")),
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("double_spec")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.exists_tac(tm("[T_num(T_i32)]")),
      @tactics.exists_tac(tm("[T_num(T_i32)]")),
      @tactics.exists_tac(tm("(NIL : List[Valtype])")),
      @tactics.exists_tac(tm("double_code")),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@tactics.first_assum(th => @tactics.accept_tac(th))),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(args : List[Value])")),
              @tactics.accept_tac(
                @bool.ispecl(
                  @list.List(
                    [
                      "(fs : List[Cl])", "(tabs : \{tabs_ty})", "(inst : Inst)", "(a : Num)", "(x : \{w})",
                      "(R : \{rty})", "(args : List[Value])",
                    ].map(tm),
                  ),
                  double_th,
                ),
              ),
            ]),
          ),
          solve(@simp.rewrite_tac(ths([@wasm.thm("n_zeros"), @lists.map(), @wasm.thm("those")]))),
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
  // apply's body: table 0 holds a at k, with type 0
  let code = program("apply_code", "[Local_get(0), Local_get(1), Call_indirect(0, 0)]")
  let table = "0 < LENGTH(inst_tabs(inst)) && tab_cl_ind(tabs, EL(0, inst_tabs(inst)), val(k)) == SOME(ConstRefFunc(a)) && cl_type(EL(a, fs)) == stypes(inst, 0)"
  let locals = "[\{i("x")}, \{i("k")}]"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && lc == \{locals} && R(gs, ms, h)"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{i("word_add(x, x)")}] && lc == \{locals} && R(gs, ms, h)"
  let vars = "∀ fs : List[Cl], ∀ tabs : \{tabs_ty}, ∀ inst : Inst, ∀ a : Num, ∀ x : \{w}, ∀ k : \{w}, ∀ R : \{rty}"
  let apply_th = sym_prove(
    "apply_body",
    "\{vars}, \{table} → sl_triple_g(double_spec(a), fs, tabs, inst, \{sa_false}, \{pre}, \{code}, \{post}, NIL)",
    [],
    [],
    specs=[spec_call],
    kind="lemma",
  )
  let th = @tactics.prove(
    tm("\{vars}, \{table} && \{native} → sl_triple_m(fs, tabs, inst, \{pre}, \{code}, \{post}, NIL)"),
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
      @tactics.exists_tac(tm("double_spec((a : Num))")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@tactics.match_mp_tac(specs), @tactics.first_assum(th => @tactics.accept_tac(th))]),
          seq([@tactics.match_mp_tac(apply_th), @simp.asm_rewrite_tac(ths([]))]),
        ]),
      ),
    ]),
  )
  record("example_indirect", th, kind="example")
  prove_apply_closed(th, table, native)
}

///|
/// apply_closed: example_indirect about runs, with no assertion left. In a
/// store whose function a is double_code and whose table (table 0 of the
/// instance) holds a at k, and a frame of the instance whose locals are
/// x and k, with a memory j, every run of apply_code either can step
/// again or has ended with x + x on the stack, the store's functions and
/// tables, the frame's instance and locals, the globals and the memory's
/// bytes as they were. From sl_triple_m_adequate_whole as fact_closed.
fn prove_apply_closed(
  example : @kernel.Thm,
  table : String,
  native : String,
) -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let exact = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => gs == gvals((s : Wstore), (f : Wframe)) && ms == mem_length(EL((j : Num), s_mems(s))) && h == heap_of(EL(j, s_mems(s)))"
  let triple = @bool.ispecl(
    @list.List(
      ["(fs : List[Cl])", "s_tabs((s : Wstore))", "(inst : Inst)", "(a : Num)", "(x : \{w})", "(k : \{w})", exact].map(tm),
    ),
    example,
  )
  let triple = @equal.conv_rule(@equal.try_conv(@equal.redepth_conv(@equal.beta_conv)), triple)
  let args = @basics.strip_comb(@basics.dest_imp(@kernel.concl(triple)).1).1.to_array()
  let adequate = @bool.ispecl(
    @list.List(
      [
        tm("(fs : List[Cl])"),
        tm("s_tabs((s : Wstore))"),
        tm("(inst : Inst)"),
        args[3],
        tm("apply_code"),
        args[5],
        tm("(j : Num)"),
        tm("(s : Wstore)"),
        tm("(f : Wframe)"),
        tm("(NIL : List[Value])"),
        tm("(s2 : Wstore)"),
        tm("(f2 : Wframe)"),
        tm("(es2 : List[Einstr])"),
      ],
    ),
    thm("sl_triple_m_adequate_whole"),
  )
  let table = table.replace_all(old="tabs,", new="s_tabs(s),")
  let th = @tactics.prove(
    tm(
      "∀ fs : List[Cl], ∀ inst : Inst, ∀ a : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ j : Num, ∀ x : \{w}, ∀ k : \{w}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], \{table} && \{native} && s_funcs(s) == fs && f_inst(f) == inst && f_locs(f) == [\{i("x")}, \{i("k")}] && smem_ind(inst) == SOME(j) && j < LENGTH(s_mems(s)) && globs_ok(s, f) && reduce_trans((s, f, MAP(Basic, apply_code)), (s2, f2, es2)) → (es2 == MAP(v_to_e, [\{i("word_add(x, x)")}]) && s_funcs(s2) == fs && s_tabs(s2) == s_tabs(s) && f_inst(f2) == inst && f_locs(f2) == f_locs(f) && gvals(s2, f2) == gvals(s, f) && heap_of(EL(j, s_mems(s2))) == heap_of(EL(j, s_mems(s)))) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2, f2, es2, s3, f3, es3))",
    ),
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(triple),
      @tactics.thenl(
        @tactics.ants_tac,
        @list.List([@simp.asm_rewrite_tac(ths([])), @tactics.disch_tac]),
      ),
      @tactics.mp_tac(adequate),
      @simp.asm_rewrite_tac(ths([@lists.map(), @lists.append()])),
      // the run ended, with vs2 the result, or it can step again
      @tactics.strip_tac,
      @tactics.first(
        @list.List([
          solve(seq([@tactics.disj1_tac, @simp.asm_rewrite_tac(ths([@lists.map()]))])),
          solve(@meson.asm_meson_tac(ths([]))),
        ]),
      ),
    ]),
  )
  record("apply_closed", th, kind="theorem")
}
