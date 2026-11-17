// Every last-live page occurs once in its correct partial list, so the four
// specialized compiled cases cover its unique predecessor/successor split.

///|
fn prove_tlsf_block_free_tail_last() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let usage = block_usage(args, p)
  let total = block_total(args, p)
  let k = "DIV(" + args[9] + "(" + p + "),8)"
  let part = args[14] + "(" + k + ")"
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
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let solveZ = (hasPrev : Bool) => {
    let prefix = if hasPrev { "(a : " + lw + ")" } else { "(NIL : " + lw + ")" }
    let label = if hasPrev { "prev" } else { "head" }
    let nil = inst(
      thm("tlsf_block_free_tail_last_" + label + "_nil"),
      ea + argv + [prefix, "(word(0) : " + w + ")", "(NIL : " + lw + ")"],
    )
    let cons = inst(
      thm("tlsf_block_free_tail_last_" + label + "_cons"),
      ea + argv + [prefix, "(nx : " + w + ")", "(tail : " + lw + ")"],
    )
    seq([
      @tactics.mp_tac(@bool.ispec(tm("(z : " + lw + ")"), @lists.list_cases())),
      @tactics.thenl(
        @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
        @list.List([
          seq([subst_vars(), free_apply(nil), small_meson(ths([]))]),
          seq([
            @tactics.first_x_assum(th => {
              if @basics.is_exists(@kernel.concl(th)) {
                @tactics.x_choose_then(tm("(nx : " + w + ")"))(
                  @tactics.x_choose_then(tm("(tail : " + lw + ")"))(th => {
                    @tactics.assume_tac(th)
                  }),
                )(th)
              } else {
                @tactics.no_tac
              }
            }),
            subst_vars(),
            free_apply(cons),
            small_meson(ths([])),
          ]),
        ]),
      ),
    ])
  }
  let _ = lemma(
    "tlsf_block_free_tail_last",
    "\{env}, \{page_quantify(vs)}\{block_old_facts(args,p,b)} && \{block_native_hyp()} && \{usage} == 1 → sl_triple_g(G,fs,tabs,inst,rp,\{before},tlsf_block_free_tail(d,free_idx),\{q},labels)",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        block_prepare(args, p, b),
        free_have(usage + " < " + total, @int.asm_arith_tac),
        free_have(
          "tlsf_count(" + p + "," + part + ") == 1",
          seq([
            @tactics.undisch_tac(tm(block_lists(args))),
            rw([thm("tlsf_small_lists_ok")]),
            small_meson(ths([])),
          ]),
        ),
        free_have(
          "MEM(" + p + "," + part + ")",
          seq([rw([thm("tlsf_count_member")]), @int.asm_arith_tac]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_member_split"), [p, part]), g),
          )(g)
        },
        @tactics.thenl(
          @class.asm_cases_tac(tm("(a : " + lw + ") == NIL")),
          @list.List([seq([subst_vars(), solveZ(false)]), solveZ(true)]),
        ),
      ])
    },
  )
}
