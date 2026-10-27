// The facts about reduction and the inversion procedure.

///|
test "facts about reduction" {
  props()
  @testkit.check_axioms()
  let statements = [
    (
      "reduce_not_vals",
      "∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], !reduce(s, f, MAP(v_to_e, vs), s', f', es')",
    ),
    (
      "reduce_not_trap",
      "∀ s : Wstore, ∀ f : Wframe, ∀ s' : Wstore, ∀ f' : Wframe, ∀ es' : List[Einstr], !reduce(s, f, [Trap], s', f', es')",
    ),
    (
      "lfilled_eq",
      "∀ k : Num, ∀ lh : Lholed, ∀ es : List[Einstr], ∀ les : List[Einstr], Lfilled(k, lh, es, les) == (k == lh_depth(lh) && les == lfill(lh, es))",
    ),
    (
      "lfilled_deterministic",
      "∀ k : Num, ∀ lh : Lholed, ∀ es : List[Einstr], ∀ l1 : List[Einstr], ∀ l2 : List[Einstr], Lfilled(k, lh, es, l1) && Lfilled(k, lh, es, l2) → l1 == l2",
    ),
    (
      "lfill_compose",
      "∀ lh : Lholed, ∀ l1 : Lholed, ∀ es : List[Einstr], lfill(lh, lfill(l1, es)) == lfill(lh_compose(lh, l1), es) && lh_depth(lh_compose(lh, l1)) == lh_depth(lh) + lh_depth(l1)",
    ),
    (
      "reduce_decompose",
      "∀ s : Wstore, ∀ f : Wframe, ∀ les : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, les, s', f', les') == (∃ lh : Lholed, ∃ e : List[Einstr], ∃ e' : List[Einstr], les == lfill(lh, e) && les' == lfill(lh, e') && reduce_base(s, f, e, s', f', e'))",
    ),
    (
      "reduce_append",
      "∀ s : Wstore, ∀ f : Wframe, ∀ es1 : List[Einstr], ∀ es2 : List[Einstr], ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, APPEND(es1, es2), s', f', les') && !ALL(is_val, es1) → (∃ es1' : List[Einstr], reduce(s, f, es1, s', f', es1') && les' == APPEND(es1', es2)) || trap_top(es1)",
    ),
    (
      "step_basic",
      "∀ s : Wstore, ∀ f : Wframe, ∀ cs : List[Einstr], ∀ x : Einstr, ∀ s' : Wstore, ∀ f' : Wframe, ∀ les' : List[Einstr], reduce(s, f, APPEND(cs, [x]), s', f', les') && ALL(is_val, cs) && !(x == Trap) && (∀ n : Num, ∀ e0 : List[Einstr], ∀ li : List[Einstr], !(x == Label(n, e0, li))) → (∃ pre : List[Einstr], ∃ suf : List[Einstr], ∃ e' : List[Einstr], cs == APPEND(pre, suf) && les' == APPEND(pre, e') && reduce_base(s, f, APPEND(suf, [x]), s', f', e'))",
    ),
  ]
  for st in statements {
    let th = thm(st.0)
    assert_true(@kernel.hyp(th).is_empty(), msg=st.0)
    assert_true(@basics.aconv(@kernel.concl(th), tm(st.1)), msg=st.0)
  }
}

///|
/// For a configuration whose instructions are values then one basic
/// instruction: the evaluator's step is the only one. Proves
/// ∀ s' f' es'. reduce(s, f, es, s', f', es') → s' == s1 && f' == f1 &&
/// es' == R from step_cases, with (s1, f1, R) the evaluator's step.
fn only_step(cfg : @kernel.Term) -> Unit raise {
  let (s, rest) = @pair.dest_pair(cfg)
  let (f, es) = @pair.dest_pair(rest)
  setup()
  guard step(s, f, es) is Stepped(ev) else { fail("the evaluator does not step") }
  let a = head_args(@kernel.concl(ev)).1
  let inv = step_cases(s, f, es)
  let s2 = @kernel.mk_var("s'", hol_type("wstore"))
  let f2 = @kernel.mk_var("f'", hol_type("wframe"))
  let es2 = @kernel.mk_var("es'", @kernel.type_of(es))
  let goal = @bool.list_mk_forall(
    @list.List([s2, f2, es2]),
    @bool.mk_imp(
      call("reduce", [s, f, es, s2, f2, es2]),
      @bool.list_mk_conj(
        @list.List([
          @basics.mk_eq(s2, a[3]),
          @basics.mk_eq(f2, a[4]),
          @basics.mk_eq(es2, a[5]),
        ]),
      ),
    ),
  )
  let _ = @tactics.prove(
    goal,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.mp_tac(@bool.mp(@bool.spec_all(inv), th))),
      // compute the side conditions of each case
      @tactics.conv_tac(@equal.rator_conv(@equal.rand_conv(eval_conv))),
      @meson.meson_tac(ths([])),
    ]),
  ) catch {
    e => {
      let d = @equal.conv_rule(
        @equal.rand_conv(eval_conv),
        @bool.spec_all(inv),
      ) catch {
        _ => inv
      }
      println("CASES " + show_term(@kernel.concl(d)))
      fail("not the only step of " + show_term(es) + ": " + e.to_string())
    }
  }
}

///|
test "inversion: the evaluator's step is the only one" {
  props()
  let programs : Array[Array[Instr]] = [
    [I32Const(10), I32Const(2), Binop(I32, Div(Signed))],
    [I32Const(1), I32Const(0), Binop(I32, Div(Signed))],
    [I32Const(8), Unop(I32, Ctz)],
    [I32Const(3), I32Const(4), Relop(I32, Less(Signed))],
    [I32Const(0), Eqz(I32)],
    [I64Const(0x1_0000_0005), I32WrapI64],
    [I32Const(1), I32Const(2), I32Const(0), Select],
    [I32Const(1), I32Const(2), I32Const(7), Select],
    [I32Const(4), Drop],
    [Nop],
    [Unreachable],
    [I32Const(0), If(Result(I32), [I32Const(10)], [I32Const(20)])],
    [I32Const(3), If(Result(I32), [I32Const(10)], [I32Const(20)])],
    [I32Const(0), BrIf(0)],
    [I32Const(1), BrIf(0)],
    [I32Const(5), BrTable([0], 1)],
    [Block(Result(I32), [I32Const(7)])],
    [Loop(NoResult, [Nop])],
    [RefNull(FuncRef)],
  ]
  let locals = [I32Val(5), I32Val(0)]
  let cfgs = programs.map(p => config(p)) +
    [
      config([LocalGet(1)], locals~),
      config([I32Const(9), LocalSet(0)], locals~),
      config([I32Const(9), LocalTee(1)], locals~),
      // a null reference (a value) and ref.is_null
      tm(
        "((s : Wstore), Wframe(NIL, (i : Inst)), [Ref(ConstNull(T_ext_ref)), Basic(Ref_is_null)])",
      ),
    ]
  let failures = []
  for c in cfgs {
    only_step(c) catch {
      e => failures.push(e.to_string())
    }
  }
  if !failures.is_empty() {
    fail(failures.join("\n"))
  }
}
