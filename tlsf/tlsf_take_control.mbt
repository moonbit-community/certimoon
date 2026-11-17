// Control flow after the search: save local 0, branch on null, and
// discard the unreachable normal continuation after a successful return.

///|
fn prove_tlsf_take_control() -> Unit raise {
  let w = w32
  let gt = "(Num, (List[Value], List[Value], Num, \{heap}) -> Bool, (List[Value], List[Value], Num, \{heap}) -> Bool) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc0 = "[(l0 : Value), (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let lc1 = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let r = "(R : \{rty})"
  let vars = "∀ m : \{w}, ∀ n : \{w}, ∀ l0 : Value, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ R : \{rty}"
  let tee = sym_prove(
    "tlsf_take_tee",
    "\{vars}, sl_triple(st([\{i("m")}], \{lc0}, \{r}), [Local_tee(0)], st([\{i("m")}], \{lc1}, \{r}))",
    [],
    () => [],
    rws=[@lists.hd(), @lists.tl()],
    kind="lemma",
  )
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, "
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let callback = "∀ ls2 : List[\{sassn}], sl_triple_g((G : \{gt}), (fs : List[Cl]), (tabs : List[(Tab_t, List[V_ref])]), (inst : Inst), (rp : \{sassn}), st(NIL, \{lc1}, \{r}), tlsf_take_success((d : \{w}), (pop : Num), (push : Num)), \{falsep}, ls2)"
  let source = inst(tee, [
    "(m : \{w})",
    "(n : \{w})",
    "(l0 : Value)",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    r,
  ])
  let both = (a : @tactics.Tactic, b : @tactics.Tactic) => {
    @tactics.thenl(@tactics.conj_tac, @list.List([a, b]))
  }
  let lift = seq([
    @tactics.match_mp_tac(thm("sl_triple_g_of")),
    both(
      call_free_tac(),
      seq([
        @tactics.match_mp_tac(thm("sl_triple_l_of")),
        @tactics.accept_tac(source),
      ]),
    ),
  ])
  let if_rule = @simp.rewrite_rule(ths([@lists.append()]))(
    inst(thm("sl_if_st_g"), [
      "(G : \{gt})",
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t, List[V_ref])])",
      "(inst : Inst)",
      "(rp : \{sassn})",
      "(NIL : List[Value])",
      lc1,
      r,
      "(m : \{w})",
      "Tbv(NONE)",
      "tlsf_take_success((d : \{w}), (pop : Num), (push : Num))",
      "(NIL : List[B_e])",
      falsep,
      "(ls : List[\{sassn}])",
    ]),
  )
  let branch = seq([
    @tactics.match_mp_tac(if_rule),
    arw([]),
    @tactics.match_mp_tac(thm("sl_block_st_g")),
    beta_goal(),
    rw([@lists.append()]),
    @tactics.first_x_assum(th => @tactics.match_accept_tac(th)),
  ])
  let rest = seq([
    @tactics.match_mp_tac(thm("sl_cons_g")),
    @tactics.exists_tac(tm(falsep)),
    both(branch, @tactics.match_accept_tac(thm("sl_false_g"))),
  ])
  let _ = lemma(
    "tlsf_take_tail_success",
    "\{env}\{vars}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ls : List[\{sassn}], !(m == word(0)) && (\{callback}) → sl_triple_g(G, fs, tabs, inst, rp, st([\{i("m")}], \{lc0}, \{r}), tlsf_take_tail(d, pop, push), \{falsep}, ls)",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_take_tail")]),
        @tactics.match_mp_tac(thm("sl_cons_g")),
        @tactics.exists_tac(tm("st([\{i("m")}], \{lc1}, \{r})")),
        both(lift, rest),
      ])
    },
  )
  let concrete_def = @simp.rewrite_conv(
    ths([
      thm("tlsf_take_tail"),
      thm("tlsf_take_success"),
      thm("tlsf_split_code"),
      @lists.append(),
    ]),
  )(tm("tlsf_take_tail((d : \{w}), (pop : Num), (push : Num))"))
  let concrete = @equal.rhs(@kernel.concl(concrete_def))
  let lc_zero = "[\{i("word(0)")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let after = "st(NIL, \{lc_zero}, \{r})"
  let raw = sym_prove(
    "tlsf_take_tail_zero_raw",
    "\{env}∀ n : \{w}, ∀ l0 : Value, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ R : \{rty}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ls : List[\{sassn}], sl_triple_g(G, fs, tabs, inst, rp, st([\{i("word(0)")}], \{lc0}, \{r}), \{show(concrete)}, st([\{i("word(0)")}], \{lc_zero}, \{r}), ls)",
    [],
    () => [],
    afters=[after, falsep, falsep, falsep],
    rws=[@lists.hd(), @lists.tl()],
    kind="lemma",
  )
  derived(
    "tlsf_take_tail_zero",
    "\{env}∀ n : \{w}, ∀ l0 : Value, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ R : \{rty}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ls : List[\{sassn}], sl_triple_g(G, fs, tabs, inst, rp, st([\{i("word(0)")}], \{lc0}, \{r}), tlsf_take_tail((d : \{w}), (pop : Num), (push : Num)), st([\{i("word(0)")}], \{lc_zero}, \{r}), ls)",
    fn() raise { @simp.rewrite_rule(ths([@equal.gsym(concrete_def)]))(raw) },
    kind="lemma",
  )
}
