///|
fn prove_tlsf_block_free_tail() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let usage = block_usage(args, p)
  let total = block_total(args, p)
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let before = "st(NIL,[" +
    i(p) +
    "," +
    i("word(" + usage + ")") +
    ",(l2 : Value)]," +
    block_pending_rty(args, p, b, "(fp : " + rty + ")") +
    ")"
  let q = "tlsf_block_free_post(" + page_arguments(vs) + ")"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let ea = [
    "(G : " + gt + ")",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(rp : " + sassn + ")",
    "(labels : List[" + sassn + "])",
    "(pop : Num)",
    "(push : Num)",
    "(free_idx : Num)",
  ]
  let apply = (name : String) => {
    seq([free_apply(inst(thm(name), ea + argv)), small_meson(ths([]))])
  }
  let _ = lemma(
    "tlsf_block_free_tail_all",
    "\{env}, \{page_quantify(vs)}\{block_old_facts(args,p,b)} && \{block_native_hyp()} → sl_triple_g(G,fs,tabs,inst,rp,\{before},tlsf_block_free_tail(d,free_idx),\{q},labels)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.thenl(
        @class.asm_cases_tac(tm(usage + " == " + total)),
        @list.List([
          apply("tlsf_block_free_tail_full"),
          @tactics.thenl(
            @class.asm_cases_tac(tm(usage + " == 1")),
            @list.List([
              apply("tlsf_block_free_tail_last"),
              apply("tlsf_block_free_tail_partial"),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
