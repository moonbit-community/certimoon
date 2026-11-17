// Close Memory::take first, then compose its verified postcondition with the
// page tail. The ambient specification contains no assumption about helpers.

///|
fn prove_tlsf_malloc_page_body() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let model = page_model_variables()
  let args = page_arguments(model)
  let pars = args +
    ",(s : " +
    w +
    "),(before : " +
    heap +
    "),(fp : " +
    rty +
    ")"
  let pre = "tlsf_malloc_page_pre(" + pars + ")"
  let post = "tlsf_malloc_page_post(" + pars + ")"
  let q = body_post(post)
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let lc = "[\{i("s")},(l1 : Value),(l2 : Value),(l3 : Value),(l4 : Value),(l5 : Value)]"
  let small = "tlsf_small((d : \{w}),(hd : \{ht}),\{page_arguments(model[8:].to_owned())})"
  let smallframe = "(gs : List[Value]) => (ms : Num) => star(\{small},(fp : \{rty})(gs,ms))"
  let large = "tlsf_large(\{page_arguments(model[0:8].to_owned())})"
  let r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && h == (before : \{heap}) && star(\{large},star(\{small},(fp : \{rty})(gs,ms)),h)"
  let p = "st(NIL,\{lc},\{r})"
  let backed = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),\{page_arguments(model[8:13].to_owned())},(lim : Num))"
  let legal = "8 <= val((s : \{w})) && val(s) <= 256 && MOD(val(s),8) == 0"
  let oldtakeargs = [
    "(d : " + w + ")",
    "(word(1080) : " + w + ")",
    "(lim : Num)",
    "(top : " + w + ")",
    "(xs : " + lw + ")",
    "(hd : " + ht + ")",
    "(fl : " + w + ")",
    "(sb : (Num) -> " + w + ")",
    "(bl : " + bt + ")",
    "(before : " + heap + ")",
    smallframe,
  ]
  let reserved = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => lc == \{lc} && tlsf_malloc_page_reserved(\{pars})(vs,gs,ms,h)"
  let env = [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : " + w + ")",
    "(pop : Num)",
    "(push : Num)",
    "(take_idx : Num)",
  ]
  let takeall = inst(
    thm("tlsf_take_all"),
    env + oldtakeargs[1:].to_owned() + ["(NIL : List[Value])", lc],
  )
  let natives = show(@basics.dest_imp(@kernel.concl(takeall)).0)
  let envvars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ pop : Num, ∀ push : Num, ∀ take_idx : Num, "
  let modelvars = page_quantify(
    model +
    [("s", w), ("before", heap), ("fp", rty)] +
    [1, 2, 3, 4, 5].map(j => ("l\{j}", "Value")),
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let constant = inst(thm("st_const"), [
    "(NIL : List[Value])",
    lc,
    r,
    "ConstInt32((word(1080) : " + w + "))",
  ])
  let ct = args_of(@kernel.concl(constant), "sl_triple", 3).unwrap()
  let prefix = lemma(
    "tlsf_malloc_page_prefix",
    "\{envvars}\{modelvars} \{backed} && \{legal} && \{natives} → sl_triple_m(fs,tabs,inst,\{p},tlsf_page_allocate_call(take_idx),\{reserved},NIL)",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_page_allocate_call")]),
        @tactics.subst1_tac(
          @equal.gsym(
            @simp.rewrite_conv(ths([@lists.append()]))(
              tm(
                "APPEND([EConstNum(ConstInt32((word(1080) : " +
                w +
                ")))],[Call((take_idx : Num))])",
              ),
            ),
          ),
        ),
        @logic.match_mp_tac(thm("sl_seq_m")),
        @tactics.exists_tac(ct[2]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_m_conseq(
              constant,
              ent_tac([@lists.append()], []),
              same_tac(),
            ),
            initialize_m_conseq(
              takeall,
              seq([
                ent_tac(
                  [
                    thm("tlsf_take_pre"),
                    @lists.append(),
                    @words.val_word(),
                    @words.dimindex_32(),
                  ],
                  [],
                ),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
              ]),
              seq([
                gen,
                beta_goal(),
                rw([@lists.append()]),
                strip,
                subst_vars(),
                arw([]),
                @logic.match_mp_tac(
                  inst(
                    thm("tlsf_malloc_page_take_post"),
                    model.map(v => "(" + v.0 + " : " + v.1 + ")") +
                    [
                      "(s : " + w + ")",
                      "(before : " + heap + ")",
                      "(fp : " + rty + ")",
                      "(vs : List[Value])",
                      "(gs : List[Value])",
                      "(ms : Num)",
                      "(h : " + heap + ")",
                    ],
                  ),
                ),
                arw([]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let focused = lemma(
    "tlsf_malloc_page_body_focused",
    "∀ G : \{gt}, \{envvars}\{modelvars} \{backed} && \{legal} && \{natives} → sl_triple_g(G,fs,tabs,inst,\{q},\{p},tlsf_page_allocate_code(take_idx),\{q},[\{q}])",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_page_allocate_call_tail")]),
        @logic.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(tm(reserved)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @logic.match_mp_tac(thm("sl_triple_g_of_m_closed")),
              free_apply(
                inst(
                  prefix,
                  env[0:3].to_owned() +
                  env[4:].to_owned() +
                  model.map(v => "(" + v.0 + " : " + v.1 + ")") +
                  [
                    "(s : " + w + ")",
                    "(before : " + heap + ")",
                    "(fp : " + rty + ")",
                  ] +
                  [1, 2, 3, 4, 5].map(j => "(l\{j} : Value)"),
                ),
              ),
            ]),
            @tactics.match_accept_tac(
              inst(
                thm("tlsf_malloc_page_tail_reserved"),
                ["(G : " + gt + ")"] +
                env[0:3].to_owned() +
                ["(take_idx : Num)"] +
                model.map(v => "(" + v.0 + " : " + v.1 + ")") +
                [
                  "(s : " + w + ")",
                  "(before : " + heap + ")",
                  "(fp : " + rty + ")",
                ] +
                [1, 2, 3, 4, 5].map(j => "(l\{j} : Value)"),
              ),
            ),
          ]),
        ),
      ])
    },
  )
  let zeros = "[" + Array::make(5, i("word(0)")).join(",") + "]"
  let focusargs = ["(G : " + gt + ")"] +
    env[0:3].to_owned() +
    env[4:].to_owned() +
    model.map(v => "(" + v.0 + " : " + v.1 + ")") +
    ["(s : " + w + ")", "(before : " + heap + ")", "(fp : " + rty + ")"] +
    Array::make(5, i("word(0)"))
  let focus = inst(focused, focusargs)
  let focusp = args_of(
      @basics.dest_imp(@kernel.concl(focus)).1,
      "sl_triple_g",
      9,
    ).unwrap()[5]
  let purep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (\{backed} && \{legal}) && (\{show(focusp)})(vs,lc,gs,ms,h)"
  let _ = lemma(
    "tlsf_malloc_page_body",
    "∀ G : \{gt}, \{envvars}" +
    page_quantify(
      model + [("s", w), ("before", heap), ("fp", rty), ("args", "List[Value]")],
    ) +
    "\{natives} → sl_triple_g(G,fs,tabs,inst,\{q},\{body_pre(pre,"(args : List[Value])",zeros)},tlsf_page_allocate_code(take_idx),\{q},[\{q}])",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_conseq_g")),
        @tactics.exists_tac(tm(purep)),
        @tactics.exists_tac(tm(q)),
        @tactics.exists_tac(tm("[" + q + "]")),
        rw([]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              ent_tac(
                [
                  thm("tlsf_malloc_page_pre"),
                  thm("tlsf_allocator"),
                  @lists.append(),
                ],
                [],
              ),
            ),
            solve(
              seq([
                @logic.match_mp_tac(thm("sl_pure_g")),
                strip,
                free_apply(focus),
              ]),
            ),
            solve(
              seq([
                gen,
                beta_goal(),
                @tactics.repeat_tac(@tactics.strip_tac),
                arw([]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
