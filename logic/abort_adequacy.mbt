// Every reachable state either satisfies the normal or specified abort
// assertion, or can take another step.

///|
fn prove_abort_adequacy() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let pre = "keep(\{env},lift((P : \{sassn}),(fr : \{hprop})),(s : Wstore),(f : Wframe),(vs : List[Value]))"
  let q = "keep(\{env},lift((Q : \{sassn}),(fr : \{hprop})))"
  let a = "((s : Wstore) => (f : Wframe) => keep(\{env},lift((A : \{sassn}),(fr : \{hprop})),s,f,NIL))"
  let code = "APPEND(MAP(v_to_e,(vs : List[Value])),MAP(Basic,(bs : List[B_e])))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ P : \{sassn}, ∀ bs : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr]"
  let stmt = "\{vars}, sl_abort_m(\{env},P,bs,Q,A) && \{pre} && reduce_trans((s,f,\{code}),(s2,f2,es2)) → (∃ res : List[Value], es2 == MAP(v_to_e,res) && \{q}(s2,f2,res)) || (es2 == [Trap] && \{a}(s2,f2)) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2,f2,es2,s3,f3,es3))"
  let _ = lemma(
    "sl_abort_m_adequate",
    stmt,
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("safe_abort_adequate")),
      @tactics.mp_tac(
        @bool.ispecl(
          @list.List(
            [
              "((s : Wstore),(f : Wframe)," + code + ")",
              "((s2 : Wstore),(f2 : Wframe),(es2 : List[Einstr]))",
            ].map(tm),
          ),
          thm("safe_abort_run"),
        ),
      ),
      arw([@pair.fst(), @pair.snd()]),
      @tactics.disch_then(th => @tactics.match_mp_tac(th)),
      @tactics.x_gen_tac(tm("(n : Num)")),
      rw([@class.eta_ax()]),
      @tactics.first_x_assum(th => {
        if show(@kernel.concl(th)).contains("sl_abort_m") {
          @tactics.match_mp_tac(
            @bool.ispecl(
              @list.List(
                [
                  "(fr : \{hprop})",
                  "(s : Wstore)",
                  "(f : Wframe)",
                  "(vs : List[Value])",
                  "(n : Num)",
                ].map(tm),
              ),
              @simp.rewrite_rule(ths([thm("sl_abort_m")]))(th),
            ),
          )
        } else {
          @tactics.no_tac
        }
      }),
      arw([]),
    ]),
  )
}
