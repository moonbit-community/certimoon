///|
fn prove_tlsf_malloc_page_body_tail() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _envvars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}"
  let _envargs = "(G : \{gt}),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),(rp : \{sassn})"
  let _orp = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (P : \{sassn})(vs,lc,gs,ms,h) || (R : \{sassn})(vs,lc,gs,ms,h)"
  let model = page_model_variables()
  let params = page_arguments(model) +
    ",(s : " +
    w +
    "),(before : " +
    heap +
    "),(fp : " +
    rty +
    ")"
  let q = body_post("tlsf_malloc_page_post(" + params + ")")
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let lc = "[\{i("s")},(l1 : Value),(l2 : Value),(l3 : Value),(l4 : Value),(l5 : Value)]"
  let p = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => lc == \{lc} && tlsf_malloc_page_reserved(\{params})(vs,gs,ms,h)"
  let env = [
    "(G : " + gt + ")",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    q,
    "(take_idx : Num)",
  ]
  let locals = [
    "(s : " + w + ")",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l3 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
  ]
  let newargs = "(d : \{w}),(lim : Num),(top2 : \{w}),(xs2 : \{lw}),(hd2 : \{ht}),(fl2 : \{w}),(sb2 : (Num) -> \{w}),(bl2 : \{bt}),\{page_arguments(model[8:].to_owned())}"
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(tlsf_allocator(\{newargs}),(fp : \{rty})(gs,ms),h)"
  let success = seq([
    free_intro(),
    g => {
      let path = inst(
        thm("tlsf_page_allocate_tail_success"),
        env +
        [
          "(p : " + w + ")",
          "val(tlsf_size((hd2 : " + ht + ")((p : " + w + "))))",
        ] +
        locals +
        [frame],
      )
      let post = seq([
        gen,
        beta_goal(),
        rw([thm("tlsf_malloc_page_post")] + lift_rws()),
        strip,
        arw([]),
        @tactics.try_tac(@tactics.disj2_tac),
        seq(
          [
            "(p : " + w + ")",
            "(top2 : " + w + ")",
            "(xs2 : " + lw + ")",
            "(hd2 : " + ht + ")",
            "(fl2 : " + w + ")",
            "(sb2 : (Num) -> " + w + ")",
            "(bl2 : " + bt + ")",
          ].map(x => @tactics.exists_tac(tm(x))),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(
          [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")] +
          lift_rws(),
        ),
      ])
      page_g_conseq(path, ent_tac([], []), post, free_apply(path))(g)
    },
  ])
  let failure = seq([
    free_intro(),
    g => {
      let pr = triple_l_terms(g.1).0
      let pr = @equal.rhs(@kernel.concl(norm_conv()(pr)))
      let st = args_of(pr, "st", 3).unwrap()
      let path = inst(
        thm("tlsf_page_allocate_tail_failure"),
        env + locals + [show(st[2])],
      )
      let callback = seq([
        gen,
        beta_goal(),
        rw([thm("tlsf_malloc_page_post")]),
        strip,
        arw([]),
        @tactics.try_tac(@tactics.disj1_tac),
        arw([]),
      ])
      let core = seq([
        @logic.match_mp_tac(@simp.rewrite_rule(ths([@class.eta_ax()]))(path)),
        callback,
      ])
      page_g_conseq(path, same_tac(), seq([gen, beta_goal(), rw([])]), core)(g)
    },
  ])
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ take_idx : Num, " +
    page_quantify(
      model +
      [("s", w), ("before", heap), ("fp", rty)] +
      [1, 2, 3, 4, 5].map(j => ("l\{j}", "Value")),
    )
  let _ = lemma(
    "tlsf_malloc_page_tail_reserved",
    "\{vars} sl_triple_g(G,fs,tabs,inst,\{q},\{p},tlsf_page_allocate_tail(take_idx),\{q},[\{q}])",
    () => {
      seq([
        gen,
        @tactics.conv_tac(
          pre_conv(
            @simp.rewrite_conv(
              ths([
                thm("tlsf_malloc_page_reserved"),
                @theorems.left_or_distrib(),
                @theorems.right_or_distrib(),
              ]),
            ),
          ),
        ),
        beta_goal(),
        @logic.match_mp_tac(thm("tlsf_page_or_g")),
        @tactics.thenl(@tactics.conj_tac, @list.List([failure, success])),
      ])
    },
  )
}
