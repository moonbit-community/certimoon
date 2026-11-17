// Compose the exact inline branch. All helper calls are discharged against
// the compiler's Memory::free, pop and push closures.

///|
fn prove_tlsf_block_free_body() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let fp = "(fp : " + rty + ")"
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
  let i32 = (x : String) => "V_num(ConstInt32((" + x + " : " + w + ")))"
  let pre = "st(NIL,[(l0 : Value)," +
    i32(b) +
    ",(l2 : Value)]," +
    block_input_rty(args, p, b, fp) +
    ")"
  let mid = "st(NIL,[" +
    i32(p) +
    "," +
    i32("word(" + block_usage(args, p) + ")") +
    ",(l2 : Value)]," +
    block_pending_rty(args, p, b, fp) +
    ")"
  let q = "tlsf_block_free_post(" + page_arguments(vs) + ")"
  let index = "(i : Num) < " +
    block_total(args, p) +
    " && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    args[9] +
    "(" +
    p +
    "),i)"
  let prefix = inst(
    thm("tlsf_block_free_release_pages"),
    ["(free_idx : Num)"] +
    args +
    [
      p,
      b,
      "(i : Num)",
      "(l0 : Value)",
      "(l2 : Value)",
      block_large_frame(args, fp),
    ],
  )
  let _ = lemma(
    "tlsf_block_free_focused",
    "\{env}, \{page_quantify(vs)}∀ i : Num, \{block_old_facts(args,p,b)} && \{block_native_hyp()} && \{index} → sl_triple_g(G,fs,tabs,inst,rp,\{pre},tlsf_block_free_code(d,free_idx),\{q},labels)",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @simp.rewrite_tac(ths([thm("tlsf_block_free_tail_parts")])),
        @tactics.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(tm(mid)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            block_g_conseq(prefix, ent_tac([], []), ent_tac([], [])),
            free_apply(inst(thm("tlsf_block_free_tail_all"), ea + argv)),
          ]),
        ),
      ])
    },
  )
}
