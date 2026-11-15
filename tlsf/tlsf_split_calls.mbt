///|
fn prove_tlsf_split_calls() -> Unit raise {
  let ft = "(List[Value], List[Value], Num, \{heap}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let pb = body_pre("(P : \{ft})", "(args : List[Value])", "(zs : List[Value])")
  let qb = body_post("(Q : \{ft})")
  def("tlsf_proved_spec", "tlsf_proved_spec((addr : Num), (code : List[B_e]), (zs : List[Value]), (nin : Num), (nout : Num), (a : Num), (P : \{ft}), (Q : \{ft})) == (a == addr && (∀ args : List[Value], sl_triple(\{pb}, code, \{qb})) && (∀ args : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, P(args, gs, ms, h) → LENGTH(args) == nin) && (∀ res : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, Q(res, gs, ms, h) → LENGTH(res) == nout))")
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ addr : Num, ∀ code : List[B_e], ∀ zs : List[Value], ∀ ts : List[Valtype], ∀ ins : List[Valtype], ∀ outs : List[Valtype]"
  let _ = lemma("tlsf_proved_specs", "\{vars}, EL(addr, fs) == Func_native(inst, Tf(ins, outs), ts, code) && n_zeros(ts) == SOME(zs) && call_free_b(code) → (∀ n : Num, specs_ok(n, tlsf_proved_spec(addr, code, zs, LENGTH(ins), LENGTH(outs)), fs, tabs, inst))", seq([
    gen, strip, @tactics.match_mp_tac(thm("sl_funs_g")),
    gen, rw([thm("tlsf_proved_spec")]), strip, subst_vars(),
    @tactics.exists_tac(tm("(ins : List[Valtype])")), @tactics.exists_tac(tm("(outs : List[Valtype])")),
    @tactics.exists_tac(tm("(ts : List[Valtype])")), @tactics.exists_tac(tm("(code : List[B_e])")),
    @tactics.exists_tac(tm("(zs : List[Value])")),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([
      solve(@tactics.first_assum(th => @tactics.accept_tac(th))),
      solve(seq([
        gen, @tactics.try_tac(strip), @tactics.match_mp_tac(thm("sl_triple_g_of")), arw([]),
        @tactics.match_mp_tac(thm("sl_triple_l_of")),
        @tactics.first_x_assum(th => @tactics.accept_tac(@bool.spec(tm("(args : List[Value])"), th))),
      ])),
      @tactics.no_tac,
    ])),
  ]))
}
