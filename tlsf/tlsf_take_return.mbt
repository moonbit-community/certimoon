// Recover the scratch locals existentially; only locals 0 and 3 have
// semantic meaning after split. The real return must read local 0.

///|
fn prove_tlsf_take_return() -> Unit raise {
  let w = w32
  let ft = "(List[Value], List[Value], Num, \{heap}) -> Bool"
  let gt = "(Num, \{ft}, \{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let rp = body_post("(Q : \{ft})")
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ Q : \{ft}, ∀ m : \{w}, ∀ n : \{w}, ∀ R : \{rty}, ∀ ls : List[\{sassn}]"
  let condition = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (R : \{rty})(gs, ms, h) → (Q : \{ft})([\{i("m")}], gs, ms, h)"
  let vc = seq([
    gen,
    @tactics.exists_tac(tm("(NIL : List[Value])")),
    rw([@lists.append()]),
    @tactics.try_tac(
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
    ),
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    arw([]),
  ])
  let raw = sym_prove(
    "tlsf_take_return_raw",
    "\{env}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, (\{condition}) → sl_triple_g(G, fs, tabs, inst, \{rp}, st(NIL, \{lc}, (R : \{rty})), [Local_get(0), Return], \{falsep}, ls)",
    [],
    [vc],
    rws=[@lists.el(), @lists.hd(), @lists.tl()],
    kind="lemma",
  )
  let pred = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == \{i("m")} && EL(3, lc) == \{i("n")} && vs == NIL && (R : \{rty})(gs, ms, h)"
  let expre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ l1 : Value, ∃ l2 : Value, ∃ l4 : Value, ∃ l5 : Value, st(NIL, \{lc}, (R : \{rty}), vs, lc, gs, ms, h)"
  let pre = seq([
    gen,
    beta_goal(),
    rw([thm("st")]),
    strip,
    seq(
      [
        "EL(1, (lc : List[Value]))", "EL(2, (lc : List[Value]))", "EL(4, (lc : List[Value]))",
        "EL(5, (lc : List[Value]))",
      ].map(x => @tactics.exists_tac(tm(x))),
    ),
    arw([]),
    @tactics.mp_tac(inst(thm("tlsf_locals_six"), ["(lc : List[Value])"])),
    arw([]),
  ])
  let core = seq(
    ["(l1 : Value)", "(l2 : Value)", "(l4 : Value)", "(l5 : Value)"].map(x => {
      seq([
        @tactics.match_mp_tac(thm("sl_ex_g")),
        beta_goal(),
        @tactics.x_gen_tac(tm(x)),
      ])
    }) +
    [
      rw([@class.eta_ax()]),
      @tactics.match_mp_tac(@simp.rewrite_rule(ths([@class.eta_ax()]))(raw)),
      arw([]),
    ],
  )
  let _ = lemma(
    "tlsf_take_return",
    "\{env}, (\{condition}) → sl_triple_g(G, fs, tabs, inst, \{rp}, \{pred}, [Local_get(0), Return], \{falsep}, ls)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(tm(expre)),
      @tactics.exists_tac(tm(falsep)),
      @tactics.exists_tac(tm("(ls : List[\{sassn}])")),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([solve(core), solve(pre), solve(same_tac())])),
    ]),
  )
}
