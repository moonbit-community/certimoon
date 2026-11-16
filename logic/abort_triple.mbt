// Separation triples with distinct normal and specified-abort postconditions.
// Both outcomes preserve the module environment and arbitrary heap frames.

///|
fn define_abort_triple() -> Unit raise {
  def(
    "sl_abort_m",
    "sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),(P : \{sassn}),(bs : List[B_e]),(Q : \{sassn}),(A : \{sassn})) == (∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ n : Num, keep(fs,tabs,inst,lift(P,fr),s,f,vs) → safe_abort(n,s,f,APPEND(MAP(v_to_e,vs),MAP(Basic,bs)),keep(fs,tabs,inst,lift(Q,fr)),(s : Wstore) => (f : Wframe) => keep(fs,tabs,inst,lift(A,fr),s,f,NIL)))",
  )
}

///|
fn prove_abort_triples() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let at = "(Wstore,Wframe) -> Bool"
  let _ = lemma(
    "safe_abort_mono",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ r : \{assn}, ∀ a : \{at}, ∀ b : \{at}, safe_abort(n,s,f,es,q,a) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s,f,vs) → r(s,f,vs)) && (∀ s : Wstore, ∀ f : Wframe, a(s,f) → b(s,f)) → safe_abort(n,s,f,es,r,b)",
    seq([
      @nums.induct_tac,
      rw([thm("safe_abort")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
          solve(
            seq([
              @tactics.disj2_tac,
              @tactics.disj1_tac,
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
          solve(
            seq([
              @tactics.disj2_tac,
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([])),
                  seq([
                    @tactics.repeat_tac(@tactics.strip_tac),
                    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                    @tactics.exists_tac(tm("(q : \{assn})")),
                    @tactics.exists_tac(tm("(a : \{at})")),
                    @meson.asm_meson_tac(ths([])),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let ent = (p : String, q : String) => {
    "∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (\{p} : \{sassn})(vs,lc,gs,ms,h) → (\{q} : \{sassn})(vs,lc,gs,ms,h)"
  }
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst"
  let _ = lemma(
    "abort_keep_lift_mono",
    "\{vars}, ∀ P : \{sassn}, ∀ Q : \{sassn}, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], (\{ent("P","Q")}) && keep(\{env},lift(P,fr),s,f,vs) → keep(\{env},lift(Q,fr),s,f,vs)",
    seq([
      gen,
      rw([thm("keep")]),
      strip,
      arw([]),
      @tactics.match_mp_tac(thm("lift_mono")),
      @tactics.exists_tac(tm("(P : \{sassn})")),
      @tactics.exists_tac(tm("(vs : List[Value])")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_abort_m_of",
    "\{vars}, ∀ P : \{sassn}, ∀ bs : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, sl_triple_m(\{env},P,bs,Q,NIL) → sl_abort_m(\{env},P,bs,Q,A)",
    seq([
      rw([thm("sl_abort_m"), thm("sl_triple_m"), thm("triple_l"), @lists.map()]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safe_abort_of_safe")),
      @tactics.match_mp_tac(thm("safel_nil")),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_abort_nil_m",
    "\{vars}, ∀ P : \{sassn}, ∀ A : \{sassn}, sl_abort_m(\{env},P,NIL,P,A)",
    seq([
      rw([thm("sl_abort_m"), @lists.map(), @lists.append_nil()]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safe_abort_vals")),
      arw([]),
    ]),
  )
  let _ = lemma(
    "sl_abort_seq_m",
    "\{vars}, ∀ P : \{sassn}, ∀ bs1 : List[B_e], ∀ Q : \{sassn}, ∀ bs2 : List[B_e], ∀ R : \{sassn}, ∀ A : \{sassn}, sl_abort_m(\{env},P,bs1,Q,A) && sl_abort_m(\{env},Q,bs2,R,A) → sl_abort_m(\{env},P,APPEND(bs1,bs2),R,A)",
    seq([
      rw([thm("sl_abort_m"), @lists.map_append(), @lists.append_assoc()]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safe_abort_seq_all")),
      @tactics.exists_tac(
        tm("keep(\{env},lift((Q : \{sassn}),(fr : \{hprop})))"),
      ),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_abort_conseq_m",
    "\{vars}, ∀ P : \{sassn}, ∀ P2 : \{sassn}, ∀ bs : List[B_e], ∀ Q : \{sassn}, ∀ Q2 : \{sassn}, ∀ A : \{sassn}, ∀ A2 : \{sassn}, (\{ent("P2","P")}) && sl_abort_m(\{env},P,bs,Q,A) && (\{ent("Q","Q2")}) && (\{ent("A","A2")}) → sl_abort_m(\{env},P2,bs,Q2,A2)",
    seq([
      rw([thm("sl_abort_m")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(thm("safe_abort_mono")),
      @tactics.exists_tac(
        tm("keep(\{env},lift((Q : \{sassn}),(fr : \{hprop})))"),
      ),
      @tactics.exists_tac(
        tm(
          "(s : Wstore) => (f : Wframe) => keep(\{env},lift((A : \{sassn}),(fr : \{hprop})),s,f,NIL)",
        ),
      ),
      beta_goal(),
      @meson.asm_meson_tac(ths([thm("abort_keep_lift_mono")])),
    ]),
  )
  let orp = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (P : \{sassn})(vs,lc,gs,ms,h) || (R : \{sassn})(vs,lc,gs,ms,h)"
  let _ = lemma(
    "sl_abort_or_m",
    "\{vars}, ∀ P : \{sassn}, ∀ R : \{sassn}, ∀ bs : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, sl_abort_m(\{env},P,bs,Q,A) && sl_abort_m(\{env},R,bs,Q,A) → sl_abort_m(\{env},\{orp},bs,Q,A)",
    seq([
      rw([
        thm("sl_abort_m"),
        thm("keep"),
        thm("lift"),
        thm("star_or"),
        @class.eta_ax(),
      ]),
      @meson.meson_tac(ths([])),
    ]),
  )
}
