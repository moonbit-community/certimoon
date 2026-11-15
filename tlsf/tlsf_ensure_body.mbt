///|
fn prove_tlsf_ensure_body() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => {
    @simp.rewrite_tac(ths([@class.eta_ax()] + xs))
  }
  let arw = (xs : Array[@kernel.Thm]) => {
    @simp.asm_rewrite_tac(ths([@class.eta_ax()] + xs))
  }
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let same = seq([gen, beta_goal(), strip, arw([])])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let d = "(d : \{w})"
  let m = "(m : \{w})"
  let s = "(s : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let model = [
    d,
    "(lim : Num)",
    "(ys : \{lw})",
    m,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
  ]
  let params = [
    d,
    s,
    "(lim : Num)",
    m,
    xs,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  let q = "tlsf_ensure_post(\{params.join(",")})"
  let rp = body_post(q)
  let ready = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && \{q}([\{i("word(1)")}],gs,ms,h)"
  let saved = "tlsf_ensure_saved(\{model.join(",")},(before : \{heap}))"
  let e = "tlsf_ensure_expected(\{s})"
  let lc = "[\{i(m)},\{i(e)}]"
  let flag = "word_and(\{hd}(\{m}),word(1))"
  let usedbody = "tlsf_ensure_used_body(\{d},(pop : Num),(push : Num))"
  let freebody = "tlsf_ensure_free_body(\{d},(pop : Num),(push : Num))"
  let labels = "[\{rp}]"
  let env = [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    rp,
  ]
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ s : \{w}, ∀ lim : Num, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let phy = "tlsf_physical_ok(\{d},(lim : Num),\{m},\{xs},\{hd})"
  let facts = "\{phy} && tlsf_bins_match(\{xs},\{hd},(bl : \{bt}))"
  let popnative = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code(\{d}))"
  let pushnative = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(\{d}))"
  let cond = "\{facts} && 16 <= val(\{s}) && val(s) <= 4160749568 && \{popnative} && \{pushnative}"
  let prefix = inst(
    thm("tlsf_ensure_prefix_saved"),
    model + ["(before : \{heap})", s, "(pop : Num)", "(push : Num)"],
  )
  let pt = args_of(@basics.dest_imp(@kernel.concl(prefix)).1, "sl_triple", 3).unwrap()
  let ifrule = @simp.rewrite_rule(ths([@lists.append(), @class.eta_ax()]))(
    inst(
      thm("sl_if_st_g"),
      env +
      [
        "(NIL : List[Value])", lc, saved, flag, "Tbv(NONE)", usedbody, freebody,
        ready, labels,
      ],
    ),
  )
  let branch = (used : Bool) => {
    let b = if used { usedbody } else { freebody }
    let block = @simp.rewrite_rule(ths([@lists.append(), @class.eta_ax()]))(
      inst(
        thm("sl_block_st_g"),
        env +
        [
          "(NIL : List[Value])", lc, saved, "(NONE : Option[Valtype])", b, ready,
          labels,
        ],
      ),
    )
    let block_premise = @basics.dest_imp(@kernel.concl(block)).0
    let bparts = args_of(block_premise, "sl_triple_g", 9).unwrap()
    let args = [
      "(G : \{gt})",
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      d,
      "(pop : Num)",
      "(push : Num)",
      "(ys : \{lw})",
      m,
      s,
      "(lim : Num)",
      hd,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(before : \{heap})",
      "(fp : \{rty})",
      show(bparts[8]),
    ]
    let use_branch = @simp.rewrite_rule(ths([@class.eta_ax()]))(
      inst(
        thm("tlsf_ensure_" + (if used { "used" } else { "free" }) + "_branch"),
        args + (if used { [] } else { ["(us : \{lw})", "(bs : \{lw})"] }),
      ),
    )
    seq([
      @tactics.disch_tac,
      have(
        (if used { "" } else { "!" }) + "tlsf_used(\{hd}(\{m}))",
        arw([thm("tlsf_used")]),
      ),
      @tactics.match_mp_tac(block),
      if used {
        @tactics.all_tac
      } else {
        seq([
          have(
            "MEM(\{m},(bl : \{bt})(tlsf_level_of(\{hd}(m)))(tlsf_slot_of(\{hd}(m))))",
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_take_bin_member"), [xs, hd, "(bl : \{bt})", m]),
              ),
              arw([@lists.mem_append(), @lists.mem()]),
            ]),
          ),
          @tactics.undisch_tac(
            tm(
              "MEM(\{m},(bl : \{bt})(tlsf_level_of(\{hd}(m)))(tlsf_slot_of(\{hd}(m))))",
            ),
          ),
          rw([@lists.mem_append_decompose()]),
          @tactics.disch_then(
            @tactics.x_choose_then(tm("(us : \{lw})"))(
              @tactics.x_choose_then(tm("(bs : \{lw})"))(th => {
                @tactics.assume_tac(th)
              }),
            ),
          ),
        ])
      },
      @tactics.match_mp_tac(use_branch),
      arw([]),
    ])
  }
  let const0 = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("sl_const"), [ready, "ConstInt32((word(1) : \{w}))"]),
  )
  let stc = args_of(@kernel.concl(const0), "sl_triple", 3).unwrap()
  let const_case = seq([
    @tactics.match_mp_tac(thm("sl_conseq_g")),
    @tactics.exists_tac(stc[0]),
    @tactics.exists_tac(stc[2]),
    @tactics.exists_tac(tm(labels)),
    rw([]),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(
      @list.List([
        solve(
          seq([
            @tactics.match_mp_tac(thm("sl_triple_g_of")),
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(call_free_tac()),
                solve(
                  seq([
                    @tactics.match_mp_tac(thm("sl_triple_l_of")),
                    @tactics.accept_tac(const0),
                  ]),
                ),
              ]),
            ),
          ]),
        ),
        solve(same),
        solve(
          seq([gen, beta_goal(), strip, subst_vars(), arw([@lists.append()])]),
        ),
      ]),
    ),
  ])
  let ifcode = "If(Tbv(NONE),\{usedbody},\{freebody})"
  let _ = lemma(
    "tlsf_ensure_body_snoc",
    "\{vars}, \{cond} → sl_triple_g(G,fs,tabs,inst,\{rp},\{show(pt[0])},tlsf_ensure_code(d,pop,push),\{rp},\{labels})",
    seq([
      gen,
      strip,
      rw([thm("tlsf_ensure_code_parts")]),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(pt[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.match_mp_tac(thm("sl_triple_g_of")),
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(call_free_tac()),
                solve(
                  seq([
                    @tactics.match_mp_tac(thm("sl_triple_l_of")),
                    @tactics.match_mp_tac(prefix),
                    arw([]),
                  ]),
                ),
              ]),
            ),
          ]),
          seq([
            @tactics.subst1_tac(
              @equal.gsym(
                @simp.rewrite_conv(ths([@lists.append()]))(
                  tm(
                    "APPEND([\{ifcode}],[EConstNum(ConstInt32((word(1) : \{w})))])",
                  ),
                ),
              ),
            ),
            @tactics.match_mp_tac(thm("sl_seq_g")),
            @tactics.exists_tac(tm(ready)),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  @tactics.match_mp_tac(ifrule),
                  @tactics.thenl(
                    @tactics.conj_tac,
                    @list.List([branch(true), branch(false)]),
                  ),
                ]),
                const_case,
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}
