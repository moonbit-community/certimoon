// Typed result blocks preserve the abort and consume their own branch target.

///|
fn prove_tlsf_start_block() -> Unit raise {
  let ar = @logic.assn
  let sa = sassn
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let code = "[Basic(Block(Tbv((ot : Option[Valtype])),(bs : List[B_e])))]"
  let enter = "[Label(LENGTH(tbv_results((ot : Option[Valtype]))),NIL,MAP(Basic,(bs : List[B_e])))]"
  let cases = @wasm.step_cases(s, f, tm(code))
  let norm = [
    @ind_types.injectivity("tf"),
    thm("tb_tf_tbv"),
    thm("tbv_results"),
    @lists.length(),
    @lists.map(),
    @lists.append(),
    @lists.append_nil(),
  ]
  let step = @simp.rewrite_rule(ths(norm))(
    inst(thm("block_step"), [
      "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(ot : Option[Valtype])",
      "(bs : List[B_e])",
    ]),
  )
  let label = @simp.rewrite_rule(ths(norm))(
    inst(thm("tlsf_safer_abort_label"), [
      "(n : Num)",
      "(ab : (Wstore,Wframe) -> Bool)",
      "(s : Wstore)",
      "(f : Wframe)",
      "(NIL : List[Value])",
      "LENGTH(tbv_results((ot : Option[Valtype])))",
      "(NIL : List[Einstr])",
      "MAP(Basic,(bs : List[B_e]))",
      "(qb : " + ar + ")",
      "(lb : " + ar + ")",
      "(q : " + ar + ")",
      "(ls : List[" + ar + "])",
      "(rq : " + ar + ")",
    ]),
  )
  let _ = startup_lemma(
    "tlsf_start_block_step",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ ot : Option[Valtype], ∀ bs : List[B_e], ∀ qb : " +
    ar +
    ", ∀ lb : " +
    ar +
    ", ∀ q : " +
    ar +
    ", ∀ ls : List[" +
    ar +
    "], ∀ rq : " +
    ar +
    ", ∀ ab : (Wstore,Wframe) -> Bool, tlsf_safer_abort(n,s,f,MAP(Basic,bs),qb,CONS(lb,ls),rq,ab) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qb(s2,f2,vs) → q(s2,f2,vs)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], lb(s2,f2,vs) → LENGTH(vs) == LENGTH(tbv_results(ot)) && q(s2,f2,vs)) → tlsf_safer_abort(SUC(n),s,f," +
    code +
    ",q,ls,rq,ab)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("tlsf_safer_abort_step")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(s),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm(enter)),
            @tactics.accept_tac(step),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.gen_tac),
            @tactics.disch_then(th => {
              @tactics.mp_tac(@drule.match_mp(cases)(th))
            }),
            @simp.asm_rewrite_tac(ths(norm)),
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm))),
            split_conjs(),
            subst_vars(),
            @tactics.match_mp_tac(label),
            startup_meson(ths([thm("tlsf_safer_abort_vals")])),
          ]),
        ]),
      ),
    ]),
  )
  let env = startup_env()
  let q = "(Q : " + sa + ")"
  let lb = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => LENGTH(vs) == LENGTH(tbv_results((ot : Option[Valtype]))) && " +
    q +
    "(vs,lc,gs,ms,h)"
  let sn = "st(NIL,(lc : List[Value]),(R : " + rty + "))"
  let _ = startup_lemma(
    "tlsf_sl_abort_r_block",
    startup_quant() +
    "∀ rp : " +
    sa +
    ", ∀ ot : Option[Valtype], ∀ lc : List[Value], ∀ R : " +
    rty +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", tlsf_sl_abort_r(" +
    env +
    ",rp," +
    sn +
    ",bs,Q,CONS(" +
    lb +
    ",ls),A) → tlsf_sl_abort_r(" +
    env +
    ",rp," +
    sn +
    ",[Block(Tbv(ot),bs)],Q,ls,A)",
    seq([
      @simp.rewrite_tac(ths([thm("tlsf_sl_abort_r")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(vs : List[Value]) == NIL",
        startup_meson(ths([thm("abort_keep_st_values")])),
      ),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.map(), @lists.append()])),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @tactics.first(
        @list.List([
          solve(@simp.rewrite_tac(ths([thm("tlsf_safer_abort")]))),
          seq([
            @tactics.match_mp_tac(thm("tlsf_start_block_step")),
            @tactics.exists_tac(
              tm("keep(" + env + ",lift(" + q + ",(fr : " + hprop + ")))"),
            ),
            @tactics.exists_tac(
              tm("keep(" + env + ",lift(" + lb + ",(fr : " + hprop + ")))"),
            ),
            @simp.rewrite_tac(ths([@lists.map()])),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(
              @list.List([
                solve(startup_meson(ths([]))),
                solve(
                  seq([
                    @simp.rewrite_tac(
                      ths([
                        thm("keep"),
                        thm("lift"),
                        thm("star_pure"),
                        @class.eta_ax(),
                      ]),
                    ),
                    startup_meson(ths([])),
                  ]),
                ),
                seq([
                  @tactics.first_assum(th => {
                    let body = @kernel.concl(th)
                    guard @basics.is_forall(body) else {
                      return @tactics.no_tac
                    }
                    let point = @bool.ispecl(
                      @list.List([
                        tm("(n' : Num)"),
                        tm("(fr : " + hprop + ")"),
                        s,
                        f,
                        tm("(NIL : List[Value])"),
                      ]),
                      th,
                    )
                    @tactics.match_mp_tac(
                      @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
                        point,
                      ),
                    )
                  }),
                  @simp.asm_rewrite_tac(ths([])),
                ]),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}
