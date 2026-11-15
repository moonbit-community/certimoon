// Compose the closed native pop call, split-and-mark, and actual return.
// This works under any ambient function specifications and labels.

///|
fn prove_tlsf_take_success() -> Unit raise {
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
  let m = "(m : \{w})"
  let n = "(n : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let oldxs = "APPEND((ys : \{lw}), CONS(\{m}, (zs : \{lw})))"
  let after = "APPEND((us : \{lw}), (bs : \{lw}))"
  let nfl = "tlsf_pop_fl(\{h}, (fl : \{w}), (sb : (Num) -> \{w}), \{after})"
  let nsb = "tlsf_pop_sb(\{h}, (sb : (Num) -> \{w}), \{after})"
  let nbl = "tlsf_pop_bl(\{h}, (bl : \{bt}), \{after})"
  let pop = inst(thm("tlsf_pop_detach"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(pop : Num)",
    "(ys : \{lw})",
    "(zs : \{lw})",
    m,
    n,
    "(lim : Num)",
    "(top : \{w})",
    hd,
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
  ])
  let split = inst(thm("tlsf_split_detached"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(push : Num)",
    "(ys : \{lw})",
    "(zs : \{lw})",
    m,
    n,
    "(lim : Num)",
    "(top : \{w})",
    hd,
    nfl,
    nsb,
    nbl,
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    "(fp : \{rty})",
  ])
  let pt = args_of(@basics.dest_imp(@kernel.concl(pop)).1, "sl_triple_m", 7).unwrap()
  let st = args_of(@basics.dest_imp(@kernel.concl(split)).1, "sl_triple_m", 7).unwrap()
  let ret_r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && tlsf_allocated((d : \{w}), lim, \{m}, \{n}, (fp : \{rty})(gs, ms), h)"
  let rp = body_post("(Q : \{ft})")
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let callback = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (\{ret_r})(gs, ms, h) → (Q : \{ft})([V_num(ConstInt32(\{m}))], gs, ms, h)"
  let pcond = @basics.dest_imp(@kernel.concl(pop)).0
  let scond = @basics.dest_imp(@kernel.concl(split)).0
  let cond = "(\{show(pcond)}) && 16 <= val(\{n}) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) <= val(tlsf_size(\{h})) && EL(sfunc_ind((inst : Inst), (push : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w}))) && (\{callback})"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ Q : \{ft}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ bs : \{lw}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}, ∀ ls : List[\{sassn}]"
  let from_module = (th : @kernel.Thm) => {
    seq([
      @tactics.match_mp_tac(thm("sl_triple_g_of_m_closed")),
      @tactics.match_mp_tac(th),
      arw([]),
    ])
  }
  let ret0 = inst(thm("tlsf_take_return"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(Q : \{ft})",
    m,
    n,
    ret_r,
    "(ls : List[\{sassn}])",
  ])
  let ret = @simp.rewrite_rule(ths([@class.eta_ax()]))(ret0)
  let _ = lemma(
    "tlsf_take_success_body",
    "\{vars}, \{cond} → sl_triple_g(G, fs, tabs, inst, \{rp}, \{show(pt[3])}, tlsf_take_success(d, pop, push), \{falsep}, ls)",
    seq([
      gen,
      strip,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([]))),
      have(
        "tlsf_bins_match(\{oldxs}, tlsf_mark(\{hd}, \{m}), \{nbl})",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_pop_bins_match"), [
              oldxs,
              hd,
              "(bl : \{bt})",
              m,
              "(us : \{lw})",
              "(bs : \{lw})",
            ]),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
        ]),
      ),
      rw([thm("tlsf_take_success")]),
      @tactics.match_mp_tac(thm("sl_seq_g")),
      @tactics.exists_tac(pt[5]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          from_module(pop),
          seq([
            @tactics.match_mp_tac(thm("sl_seq_g")),
            @tactics.exists_tac(st[5]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                from_module(split),
                seq([rw([@class.eta_ax()]), @tactics.match_mp_tac(ret), arw([])]),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  ignore(scond)
}
