///|
fn prove_tlsf_free_start() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let nh = "tlsf_release((hd : \{ht}),(m : \{w}))"
  let raw = inst(thm("tlsf_free_begin"), [
    "(ys : \{lw})",
    "(zs : \{lw})",
    "(m : \{w})",
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(lim : Num)",
    "(top : \{w})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(l1 : Value)",
    "(l2 : Value)",
    "(fp : \{rty})",
  ])
  let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple", 3).unwrap()
  let goal = "tlsf_free_work((d : \{w}),(lim : Num),(m : \{w}),\{xs},(hd : \{ht}),(fp : \{rty}),F,F)"
  let fold = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("tlsf_free_work_fold"), [
      "(d : \{w})",
      "(lim : Num)",
      "(m : \{w})",
      xs,
      "(hd : \{ht})",
      "(fp : \{rty})",
      "F",
      "F",
      "(top : \{w})",
      "(ys : \{lw})",
      "(m : \{w})",
      "(zs : \{lw})",
      nh,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(l1 : Value)",
      "(l2 : Value)",
    ]),
  )
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let cond = "tlsf_physical_ok((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht})) && tlsf_used(hd(m)) && tlsf_bins_match(\{xs},hd,(bl : \{bt}))"
  let same = seq([gen, beta_goal(), strip, arw([])])
  let _ = lemma(
    "tlsf_free_start",
    "\{vars}, \{cond} → sl_triple_g(G,fs,tabs,inst,rp,\{show(rt[0])},tlsf_free_clear(d,pop,push),\{goal},labels)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_free_begin_model"), [
          xs,
          "(m : \{w})",
          "(d : \{w})",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
          "(bl : \{bt})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(rt[0]),
      @tactics.exists_tac(rt[2]),
      @tactics.exists_tac(tm("(labels : List[\{sassn}])")),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(same),
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
                      @tactics.match_mp_tac(raw),
                      arw([]),
                    ]),
                  ),
                ]),
              ),
            ]),
          ),
          solve(
            seq([
              rw([@class.eta_ax()]),
              @tactics.match_mp_tac(fold),
              arw([
                thm("tlsf_free_release_live"),
                thm("tlsf_free_release_covers"),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
