// Consequence for the return-aware abort judgment.

///|
fn prove_tlsf_start_mono() -> Unit raise {
  let a = @logic.assn
  let safer = thm("tlsf_safer_abort")
  let weaker = (l : String, l2 : String) => {
    "LENGTH(\{l2}) == LENGTH(\{l}) && (∀ i : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], i < LENGTH(\{l}) && EL(i, \{l}, s, f, vs) → EL(i, \{l2}, s, f, vs))"
  }
  let mono_ih = seq([
    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
    @tactics.exists_tac(tm("(ab : (Wstore,Wframe) -> Bool)")),
    @tactics.exists_tac(tm("(q : \{a})")),
    @tactics.exists_tac(tm("(l : List[\{a}])")),
    @tactics.exists_tac(tm("(rq : \{a})")),
    startup_meson(ths([])),
  ])
  let _ = startup_lemma(
    "tlsf_safer_abort_mono",
    "∀ n : Num, ∀ ab : (Wstore,Wframe) -> Bool, ∀ ab2 : (Wstore,Wframe) -> Bool, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{a}, ∀ q2 : \{a}, ∀ l : List[\{a}], ∀ l2 : List[\{a}], ∀ rq : \{a}, ∀ rq2 : \{a}, (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) && \{weaker("l", "l2")} && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], rq(s, f, vs) → rq2(s, f, vs)) && (∀ s : Wstore, ∀ f : Wframe, ab(s,f) → ab2(s,f)) && tlsf_safer_abort(n, s, f, es, q, l, rq, (ab : (Wstore,Wframe) -> Bool)) → tlsf_safer_abort(n, s, f, es, q2, l2, rq2, (ab2 : (Wstore,Wframe) -> Bool))",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safer])),
        seq([
          @simp.rewrite_tac(ths([safer])),
          @tactics.thenl(
            @tactics.repeat_tac(@tactics.strip_tac),
            @list.List([
              seq([
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                startup_meson(ths([])),
              ]),
              seq([
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(i : Num)")),
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(tm("(lh : Lholed)")),
                @tactics.thenl(
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @list.List([
                    @simp.asm_rewrite_tac(ths([])),
                    @simp.asm_rewrite_tac(ths([])),
                    seq([
                      @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                      @simp.asm_rewrite_tac(ths([])),
                    ]),
                    seq([@tactics.repeat_tac(@tactics.strip_tac), mono_ih]),
                  ]),
                ),
              ]),
              seq([
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm("(vs : List[Value])")),
                @tactics.exists_tac(tm("(lh : Lholed)")),
                startup_meson(ths([])),
              ]),
              seq([
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                startup_meson(ths([])),
              ]),
              startup_steps(startup_meson(ths([])), mono_ih),
            ]),
          ),
        ]),
      ]),
    ),
  )
}
