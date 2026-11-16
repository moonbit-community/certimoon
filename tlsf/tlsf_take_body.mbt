// Compose the compiled search block with both take tails. The search
// keeps the entire heap exact until a nonzero candidate is detached.

///|
fn prove_tlsf_take_composition() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value], List[Value], Num, \{heap}) -> Bool"
  let gt = "(Num, \{ft}, \{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let same = seq([gen, beta_goal(), strip, arw([])])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let params = [
    "(d : \{w})",
    "(s : \{w})",
    "(lim : Num)",
    "(top : \{w})",
    "(xs : \{lw})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  let ps = params.join(", ")
  let q = "tlsf_take_post(\{ps})"
  let rp = body_post(q)
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && h == (before : \{heap}) && star(\{large}, (fp : \{rty})(gs, ms), h)"
  let n = "tlsf_align((s : \{w}))"
  let query = "tlsf_search((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let lc0 = "[(l0 : Value), (l1 : Value), (l2 : Value), \{i(n)}, (l4 : Value), (l5 : Value)]"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let facts = "tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht})) && tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt})) && tlsf_tables_sync((fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let popnative = "EL(sfunc_ind((inst : Inst), (pop : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], NIL), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_pop_code((d : \{w})))"
  let pushnative = "EL(sfunc_ind((inst : Inst), (push : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let cond = "16 <= val((s : \{w})) && val(s) <= 4160749568 && \{popnative} && \{pushnative} && \{facts}"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ s : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let ls = "[\{rp}]"
  let consequence = (
    p : @kernel.Term,
    q0 : @kernel.Term,
    core : @tactics.Tactic,
    pre : @tactics.Tactic,
    post : @tactics.Tactic,
  ) => {
    seq([
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(p),
      @tactics.exists_tac(q0),
      @tactics.exists_tac(tm(ls)),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([solve(core), solve(pre), solve(post), solve(same)]),
      ),
    ])
  }
  let zero = inst(thm("tlsf_take_tail_zero"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    rp,
    n,
    "(l0 : Value)",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    r,
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    ls,
  ])
  let zt = args_of(@kernel.concl(zero), "sl_triple_g", 9).unwrap()
  let zero_case = seq([
    arw([]),
    consequence(
      zt[5],
      zt[7],
      @tactics.accept_tac(zero),
      same,
      seq([gen, rw([thm("st"), thm("tlsf_take_post")]), strip, arw([])]),
    ),
  ])
  let success = inst(thm("tlsf_take_success_body"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    q,
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(ys : \{lw})",
    "(zs : \{lw})",
    "(m : \{w})",
    n,
    "(lim : Num)",
    "(top : \{w})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(us : \{lw})",
    "(bs : \{lw})",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    "(fp : \{rty})",
    "(ls2 : List[\{sassn}])",
  ])
  let st = args_of(@basics.dest_imp(@kernel.concl(success)).1, "sl_triple_g", 9).unwrap()
  let result_vars = "∀ d : \{w}, ∀ s : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let finish = lemma(
    "tlsf_take_allocated_post",
    "\{result_vars}, ∀ m : \{w}, ∀ n : \{w}, ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, ms == (lim : Num) && \{query} == m && MEM(m,(xs : \{lw})) && !tlsf_used((hd : \{ht})(m)) && val((s : \{w})) <= val(n) && tlsf_allocated((d : \{w}),lim,m,n,(xs : \{lw}),(hd : \{ht}),(fp : \{rty})(gs,ms),h) → \{q}([\{i("m")}],gs,ms,h)",
    seq([
      gen,
      strip,
      have(
        "tlsf_allocated((d : \{w}),(lim : Num),(m : \{w}),(s : \{w}),(xs : \{lw}),(hd : \{ht}),(fp : \{rty})((gs : List[Value]),(ms : Num)),(h : \{heap}))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_allocated_mono"), [
              "(d : \{w})",
              "(lim : Num)",
              "(m : \{w})",
              "(n : \{w})",
              "(s : \{w})",
              "(xs : \{lw})",
              "(hd : \{ht})",
              "(fp : \{rty})((gs : List[Value]), (ms : Num))",
              "(h : \{heap})",
            ]),
          ),
          arw([]),
        ]),
      ),
      rw([thm("tlsf_take_post")]),
      beta_goal(),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let finish_inst = inst(
    finish,
    params +
    ["(m : \{w})", n, "(gs : List[Value])", "(ms : Num)", "(h : \{heap})"],
  )
  let callback = seq([
    gen,
    beta_goal(),
    strip,
    @tactics.match_mp_tac(finish_inst),
    arw([@lists.mem_append(), @lists.mem()]),
  ])
  let success_core = seq([
    @tactics.match_mp_tac(thm("tlsf_take_tail_success")),
    arw([]),
    @tactics.x_gen_tac(tm("(ls2 : List[\{sassn}])")),
    // The successful path can drop the saved-heap equality used by search.
    @tactics.match_mp_tac(thm("sl_conseq_g")),
    @tactics.exists_tac(st[5]),
    @tactics.exists_tac(tm(falsep)),
    @tactics.exists_tac(tm("(ls2 : List[\{sassn}])")),
    rw([]),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(
      @list.List([
        solve(seq([@tactics.match_mp_tac(success), arw([]), callback])),
        solve(ent_tac([], [])),
        solve(same),
      ]),
    ),
  ])
  let nonzero_case = seq([
    @tactics.mp_tac(
      inst(thm("tlsf_search_aligned_sound"), [
        "(s : \{w})",
        "(d : \{w})",
        "(lim : Num)",
        "(top : \{w})",
        "(xs : \{lw})",
        "(hd : \{ht})",
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
      ]),
    ),
    arw([thm("tlsf_find_result")]),
    strip,
    have(
      "MEM((m : \{w}), (bl : \{bt})(tlsf_level_of((hd : \{ht})(m)))(tlsf_slot_of(hd(m))))",
      seq([
        @tactics.match_mp_tac(
          inst(thm("tlsf_take_bin_member"), [
            "(xs : \{lw})",
            "(hd : \{ht})",
            "(bl : \{bt})",
            "(m : \{w})",
          ]),
        ),
        arw([]),
      ]),
    ),
    @tactics.undisch_tac(tm("MEM((m : \{w}), (xs : \{lw}))")),
    rw([@lists.mem_append_decompose()]),
    @tactics.disch_then(
      @tactics.x_choose_then(tm("(ys : \{lw})"))(
        @tactics.x_choose_then(tm("(zs : \{lw})"))(th => @tactics.assume_tac(th)),
      ),
    ),
    @tactics.undisch_tac(
      tm(
        "MEM((m : \{w}), (bl : \{bt})(tlsf_level_of((hd : \{ht})(m)))(tlsf_slot_of(hd(m))))",
      ),
    ),
    rw([@lists.mem_append_decompose()]),
    @tactics.disch_then(
      @tactics.x_choose_then(tm("(us : \{lw})"))(
        @tactics.x_choose_then(tm("(bs : \{lw})"))(th => @tactics.assume_tac(th)),
      ),
    ),
    // Retain the symbolic m and rewrite xs to its physical decomposition.
    @tactics.rule_assum_tac(th => {
      if @basics.aconv(
          @kernel.concl(th),
          tm(
            "(xs : \{lw}) == APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))",
          ),
        ) {
        th
      } else {
        @simp.rewrite_rule(
          ths([
            @kernel.assume_rule(
              tm(
                "(xs : \{lw}) == APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))",
              ),
            ),
          ]),
        )(th)
      }
    }),
    consequence(
      tm("st([\{i("m")}], \{lc0}, \{r})"),
      tm(falsep),
      success_core,
      same,
      seq([gen, beta_goal(), rw([])]),
    ),
  ])
  let _ = lemma(
    "tlsf_take_tail_found",
    "\{vars}, ∀ m : \{w}, ∀ l0 : Value, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, \{cond} && \{query} == m → sl_triple_g(G, fs, tabs, inst, \{rp}, st([\{i("m")}], \{lc0}, \{r}), tlsf_take_tail(d, pop, push), \{rp}, \{ls})",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_align_bounds"), ["(s : \{w})"])),
      arw([]),
      strip,
      have("16 <= val(\{n})", @int.asm_arith_tac),
      @tactics.mp_tac(inst(thm("tlsf_align_mod"), ["(s : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(m : \{w}) == word(0)")),
        @list.List([zero_case, nonzero_case]),
      ),
    ]),
  )
  let find = inst(thm("tlsf_find_all"), [
    params[1],
    params[0],
    params[2],
    params[3],
    params[4],
    params[5],
    params[6],
    params[7],
    params[8],
    params[9],
    params[10],
  ])
  let findparts = args_of(
    @basics.dest_imp(@kernel.concl(find)).1,
    "sl_triple",
    3,
  ).unwrap()
  let exvars = [
    "(m : \{w})",
    "(l0 : Value)",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
  ]
  let expr = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ m : \{w}, ∃ l0 : Value, ∃ l1 : Value, ∃ l2 : Value, ∃ l4 : Value, ∃ l5 : Value, \{query} == m && st([\{i("m")}], \{lc0}, \{r}, vs, lc, gs, ms, h)"
  let tail_pre = seq([
    gen,
    beta_goal(),
    strip,
    @tactics.exists_tac(tm(query)),
    seq(
      [0, 1, 2, 4, 5].map(k => {
        @tactics.exists_tac(tm("EL(\{k}, (lc : List[Value]))"))
      }),
    ),
    arw([thm("st")]),
    @tactics.mp_tac(inst(thm("tlsf_locals_six"), ["(lc : List[Value])"])),
    arw([]),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw([]),
    @meson.meson_tac(ths([])),
  ])
  let tail_core = seq(
    [] +
    exvars.map(x => {
      seq([
        @tactics.match_mp_tac(thm("sl_ex_g")),
        beta_goal(),
        @tactics.x_gen_tac(tm(x)),
      ])
    }) +
    [
      @tactics.match_mp_tac(thm("sl_pure_g")),
      @tactics.disch_tac,
      rw([@class.eta_ax()]),
      @tactics.match_mp_tac(
        @simp.rewrite_rule(ths([@class.eta_ax()]))(thm("tlsf_take_tail_found")),
      ),
      arw([]),
    ],
  )
  let _ = lemma(
    "tlsf_take_body_focused",
    "\{vars}, \{cond} → sl_triple_g(G, fs, tabs, inst, \{rp}, \{show(findparts[0])}, tlsf_take_code(d, pop, push), \{rp}, \{ls})",
    seq([
      gen,
      strip,
      rw([thm("tlsf_take_code_parts")]),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(findparts[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.match_mp_tac(thm("sl_triple_g_of")),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                call_free_tac(),
                seq([
                  @tactics.match_mp_tac(thm("sl_triple_l_of")),
                  @tactics.match_mp_tac(find),
                  arw([]),
                ]),
              ]),
            ),
          ]),
          consequence(tm(expr), tm(rp), tail_core, tail_pre, same),
        ]),
      ),
    ]),
  )
}
