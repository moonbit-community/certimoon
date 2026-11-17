// Regressions for typed abort composition and state predicates that mention
// the operand stack whose value has already been fixed by an equality.

///|
fn prove_abort_symbolic_examples() -> Unit raise {
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ n : " +
    w32 +
    ", ∀ lc : List[Value], ∀ R : " +
    rty +
    ", "
  let i = (x : String) => "V_num(ConstInt32((" + x + " : " + w32 + ")))"
  let p = "st(NIL,(lc : List[Value]),(R : " + rty + "))"
  let q = "st([" + i("word(42)") + "],(lc : List[Value]),(R : " + rty + "))"
  let code = "[EConstNum(ConstInt32((n : " +
    w32 +
    "))),If(Tbv(SOME(T_num(T_i32))),[Unreachable],[EConstNum(ConstInt32((word(42) : " +
    w32 +
    ")))])]"
  let vc = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([thm("st")])),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let _ = lemma(
    "example_abort_typed_if",
    vars +
    "sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    p +
    "," +
    code +
    "," +
    q +
    "," +
    p +
    ")",
    seq([@tactics.repeat_tac(@tactics.gen_tac), abort_sym_tac([], vc)]),
  )
  let fprop = "(List[Value],List[Value],Num," + heap + ") -> Bool"
  let frame = "(gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (P : " +
    fprop +
    ")([" +
    i("(x : " + w32 + ")") +
    "],gs,ms,h)"
  let before = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => vs == [" +
    i("(x : " + w32 + ")") +
    "] && lc == (lc0 : List[Value]) && (P : " +
    fprop +
    ")(vs,gs,ms,h)"
  ignore(
    sym_prove(
      "example_stack_in_heap_predicate",
      "∀ P : " +
      fprop +
      ", ∀ x : " +
      w32 +
      ", ∀ lc0 : List[Value], sl_triple(" +
      before +
      ",[Drop],st(NIL,(lc0 : List[Value])," +
      frame +
      "))",
      [],
      [vc],
      kind="example",
    ),
  )
}
