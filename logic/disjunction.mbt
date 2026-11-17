// Case analysis on an assertion's alternatives preserves the same control context.

///|
fn prove_disjunctive_triple() -> Unit raise {
  let gt = "(Num," + fprop + "," + fprop + ") -> Bool"
  let env = "(G : " +
    gt +
    "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),(rp : " +
    sassn +
    ")"
  let either = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (P : " +
    sassn +
    ")(vs,lc,gs,ms,h) || (R : " +
    sassn +
    ")(vs,lc,gs,ms,h)"
  let _ = lemma(
    "sl_or_g",
    "∀ G : " +
    gt +
    ", ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : " +
    sassn +
    ", ∀ P : " +
    sassn +
    ", ∀ R : " +
    sassn +
    ", ∀ Q : " +
    sassn +
    ", ∀ bs : List[B_e], ∀ ls : List[" +
    sassn +
    "], sl_triple_g(" +
    env +
    ",P,bs,Q,ls) && sl_triple_g(" +
    env +
    ",R,bs,Q,ls) → sl_triple_g(" +
    env +
    "," +
    either +
    ",bs,Q,ls)",
    seq([
      @simp.rewrite_tac(
        ths([
          thm("sl_triple_g"),
          thm("keep"),
          thm("lift"),
          thm("star_or"),
          @class.eta_ax(),
        ]),
      ),
      @meson.meson_tac(ths([])),
    ]),
  )
}

///|
fn prove_disjunctive_example() -> Unit raise {
  let gt = "(Num," + fprop + "," + fprop + ") -> Bool"
  let i = (n : String) => "V_num(ConstInt32((word(" + n + ") : " + w32 + ")))"
  let pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => lc == (locals : List[Value]) && (R : " +
    rty +
    ")(gs,ms,h) && (vs == [" +
    i("1") +
    "] || vs == [" +
    i("2") +
    "])"
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths([])),
  ])
  ignore(
    sym_prove(
      "example_general_disjunction",
      "∀ G : " +
      gt +
      ", ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : " +
      sassn +
      ", ∀ locals : List[Value], ∀ R : " +
      rty +
      ", ∀ ls : List[" +
      sassn +
      "], sl_triple_g(G,fs,tabs,inst,rp," +
      pre +
      ",[Drop],st(NIL,locals,R),ls)",
      [],
      [same, same],
    ),
  )
}
