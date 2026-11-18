// Closed module triples supporting returns and branches as well as an abort.
// Function specifications are already discharged in every supplied fragment.

///|
fn startup_env() -> String {
  "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
}

///|
fn startup_quant() -> String {
  "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, "
}

///|
fn startup_false_specs() -> String {
  "(j : Num) => (P : " + @logic.fprop + ") => (Q : " + @logic.fprop + ") => F"
}

///|
fn define_tlsf_start_logic() -> Unit raise {
  let sa = sassn
  def(
    "tlsf_sl_abort_r",
    "tlsf_sl_abort_r(" +
    startup_env() +
    ",(rp : " +
    sa +
    "),(P : " +
    sa +
    "),(bs : List[B_e]),(Q : " +
    sa +
    "),(ls : List[" +
    sa +
    "]),(A : " +
    sa +
    ")) == (∀ n : Num, ∀ fr : " +
    hprop +
    ", ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], keep(fs,tabs,inst,lift(P,fr),s,f,vs) → tlsf_safer_abort(n,s,f,APPEND(MAP(v_to_e,vs),MAP(Basic,bs)),keep(fs,tabs,inst,lift(Q,fr)),MAP(keep(fs,tabs,inst),MAP((x : " +
    sa +
    ") => lift(x,fr),ls)),keep(fs,tabs,inst,lift(rp,fr)),(s : Wstore) => (f : Wframe) => keep(fs,tabs,inst,lift(A,fr),s,f,NIL)))",
  )
}

///|
fn prove_tlsf_start_logic() -> Unit raise {
  let sa = sassn
  let ar = @logic.assn
  let at = "(Wstore,Wframe) -> Bool"
  let env = startup_env()
  let quant = startup_quant()
  let tr = (p : String, code : String, q : String) => {
    "tlsf_sl_abort_r(" +
    env +
    ",(rp : " +
    sa +
    ")," +
    p +
    "," +
    code +
    "," +
    q +
    ",(ls : List[" +
    sa +
    "]),(A : " +
    sa +
    "))"
  }
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let strip = @tactics.repeat_tac(@tactics.strip_tac)
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _ = startup_lemma(
    "tlsf_safer_abort_to_abort",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : " +
    ar +
    ", ∀ rq : " +
    ar +
    ", ∀ ab : " +
    at +
    ", (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], !rq(s2,f2,vs)) && tlsf_safer_abort(n,s,f,es,q,NIL,rq,ab) → safe_abort(n,s,f,es,q,ab)",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_safer_abort"),
        thm("safe_abort"),
        @lists.length(),
        @arith.lt(),
      ]),
      strip,
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_start_empty_specs",
    quant + "∀ n : Num, specs_ok(n," + startup_false_specs() + "," + env + ")",
    seq([rw([thm("specs_ok")])]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_of_g",
    quant +
    "∀ G : " +
    @logic.specs_ty +
    ", ∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", (∀ n : Num, specs_ok(n,G," +
    env +
    ")) && sl_triple_g(G," +
    env +
    ",rp,P,bs,Q,ls) → " +
    tr("P", "bs", "Q"),
    seq([
      rw([thm("tlsf_sl_abort_r"), thm("sl_triple_g")]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_of_safer")),
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_of_m",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", sl_abort_m(" +
    env +
    ",P,bs,Q,A) → " +
    tr("P", "bs", "Q"),
    seq([
      rw([thm("tlsf_sl_abort_r"), thm("sl_abort_m")]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_of_abort")),
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_m_of_r",
    quant +
    "∀ P : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ A : " +
    sa +
    ", tlsf_sl_abort_r(" +
    env +
    "," +
    malloc_false() +
    ",P,bs,Q,NIL,A) → sl_abort_m(" +
    env +
    ",P,bs,Q,A)",
    seq([
      rw([thm("tlsf_sl_abort_r"), thm("sl_abort_m"), @lists.map()]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_to_abort")),
      @tactics.exists_tac(
        tm(
          "keep(" + env + ",lift(" + malloc_false() + ",(fr : " + hprop + ")))",
        ),
      ),
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(rw([thm("keep"), thm("lift"), thm("star")])),
          solve(startup_meson(ths([]))),
        ]),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_seq",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ bs1 : List[B_e], ∀ Q : " +
    sa +
    ", ∀ bs2 : List[B_e], ∀ R : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", " +
    tr("P", "bs1", "Q") +
    " && " +
    tr("Q", "bs2", "R") +
    " → " +
    tr("P", "APPEND(bs1,bs2)", "R"),
    seq([
      rw([thm("tlsf_sl_abort_r"), @lists.map_append(), @lists.append_assoc()]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_seq")),
      @tactics.exists_tac(
        tm("keep(" + env + ",lift((Q : " + sa + "),(fr : " + hprop + ")))"),
      ),
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_nil",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", " +
    tr("P", "NIL", "P"),
    seq([
      rw([thm("tlsf_sl_abort_r"), @lists.map(), @lists.append_nil()]),
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_vals")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_pure",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ P : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", ∀ c : Bool, (c → " +
    tr("P", "bs", "Q") +
    ") → " +
    tr(
      "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => c && P(vs,lc,gs,ms,h)",
      "bs",
      "Q",
    ),
    seq([
      rw([thm("tlsf_sl_abort_r"), thm("keep"), thm("lift_pure")]),
      startup_meson(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_sl_abort_r_false",
    quant +
    "∀ rp : " +
    sa +
    ", ∀ bs : List[B_e], ∀ Q : " +
    sa +
    ", ∀ ls : List[" +
    sa +
    "], ∀ A : " +
    sa +
    ", " +
    tr(malloc_false(), "bs", "Q"),
    seq([rw([thm("tlsf_sl_abort_r"), thm("keep"), thm("lift"), thm("star")])]),
  )
  let _ = gen
}
