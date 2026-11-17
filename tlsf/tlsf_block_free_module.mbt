// Closed verification of the compiler's inline Block::free branch. Its
// surrounding public free guard/dispatch/drop are outside this contract.

///|
fn prove_tlsf_block_free_module() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let p0 = "tlsf_block_free_pre(" + page_arguments(vs) + ")"
  let q0 = "tlsf_block_free_post(" + page_arguments(vs) + ")"
  let i32 = "V_num(ConstInt32(" + b + "))"
  let raw = "st(NIL,[(l0 : Value)," +
    i32 +
    ",(l2 : Value)]," +
    block_input_rty(a, p, b, fp) +
    ")"
  let index = "(i : Num) < " +
    block_total(a, p) +
    " && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    a[9] +
    "(" +
    p +
    "),i)"
  let pp = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (∃ i : Num, " +
    block_old_facts(a, p, b) +
    " && " +
    index +
    " && (" +
    raw +
    ")(vs,lc,gs,ms,h))"
  let pp = show(
    @equal.rhs(@kernel.concl(@simp.rewrite_conv(ths([thm("st")]))(tm(pp)))),
  )
  let client = small_star([
    block_pages(a),
    block_table(a),
    "tlsf_bytes(val(" + b + ")+8," + a[9] + "(" + p + "))",
    "(" + fp + ")((gs : List[Value]),(lim : Num))",
  ])
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let pre = seq([
    gen,
    beta_goal(),
    rw(
      [
        thm("tlsf_block_free_pre"),
        thm("tlsf_allocator_frame"),
        thm("tlsf_small"),
      ] +
      lift_rws(),
    ),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    subst_only("vs"),
    subst_only("lc"),
    subst_only("ms"),
    free_have(
      "val(" + a[0] + ") <= 4294965088",
      seq([
        @tactics.match_mp_tac(
          inst(
            thm("tlsf_block_free_large_bound"),
            a + [client, "(h : " + heap + ")"],
          ),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(ac),
      ]),
    ),
    g => {
      @tactics.strip_assume_tac(
        block_under(inst(thm("tlsf_small_live_slot"), a + [p, b]), g),
      )(g)
    },
    @tactics.exists_tac(tm("(i : Num)")),
    arw([thm("st")] + lift_rws() + ac),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw(ac),
  ])
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
  let body = lemma(
    "tlsf_block_free_body",
    "∀ G : " +
    gt +
    ", " +
    env +
    ", ∀ rp : " +
    sassn +
    ", ∀ labels : List[" +
    sassn +
    "], " +
    page_quantify(vs) +
    block_native_hyp() +
    " → sl_triple_g(G,fs,tabs,inst,rp," +
    p0 +
    ",tlsf_block_free_code(d,free_idx)," +
    q0 +
    ",labels)",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(thm("sl_conseq_g")),
        @tactics.exists_tac(tm(pp)),
        @tactics.exists_tac(tm(q0)),
        @tactics.exists_tac(tm("(labels : List[" + sassn + "])")),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_at("block entry", pre),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  free_intro(),
                  free_apply(
                    inst(
                      thm("tlsf_block_free_focused"),
                      ea + argv + ["(i : Num)"],
                    ),
                  ),
                ]),
                seq([
                  rw([]),
                  gen,
                  beta_goal(),
                  @tactics.repeat_tac(@tactics.strip_tac),
                  arw([]),
                ]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let empty = "(a : Num) => (P : " + ft + ") => (Q : " + ft + ") => F"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => F"
  let _ = lemma(
    "tlsf_block_free_all",
    env +
    ", " +
    page_quantify(vs) +
    block_native_hyp() +
    " → sl_triple_m(fs,tabs,inst," +
    p0 +
    ",tlsf_block_free_code(d,free_idx)," +
    q0 +
    ",NIL)",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
        @tactics.exists_tac(tm(empty)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            rw([thm("specs_ok")]),
            free_apply(
              inst(
                body,
                [
                  empty,
                  "(fs : List[Cl])",
                  "(tabs : List[(Tab_t,List[V_ref])])",
                  "(inst : Inst)",
                  "(pop : Num)",
                  "(push : Num)",
                  "(free_idx : Num)",
                  falsep,
                  "(NIL : List[" + sassn + "])",
                ] +
                argv,
              ),
            ),
          ]),
        ),
      ])
    },
  )
}
