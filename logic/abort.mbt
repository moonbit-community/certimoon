// Safety with a specified abort. Ordinary triples still exclude every trap;
// this separate judgement accounts for deliberate allocation-failure aborts.

///|
fn define_abort() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  def(
    "safe_abort",
    "safe_abort(0,(s : Wstore),(f : Wframe),(es : List[Einstr]),(q : \{assn}),(a : \{at})) == T && safe_abort(SUC(n),s,f,es,q,a) == ((∃ vs : List[Value], es == MAP(v_to_e,vs) && q(s,f,vs)) || (es == [Trap] && a(s,f)) || ((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → safe_abort(n,s2,f2,es2,q,a))))",
  )
}

///|
fn prove_abort_basics() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let sa = thm("safe_abort")
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ a : \{at}"
  let _ = lemma(
    "safe_abort_of_safe",
    "∀ n : Num, \{vars}, safe(n,s,f,es,q) → safe_abort(n,s,f,es,q,a)",
    seq([
      @nums.induct_tac,
      rw([sa, thm("safe")]),
      gen,
      strip,
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "safe_abort_vals",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : \{assn}, ∀ a : \{at}, q(s,f,vs) → safe_abort(n,s,f,MAP(v_to_e,vs),q,a)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("safe_abort_of_safe")),
      @tactics.match_mp_tac(thm("safe_vals")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "safe_abort_trap",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, ∀ a : \{at}, a(s,f) → safe_abort(n,s,f,[Trap],q,a)",
    seq([
      gen,
      strip,
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      rw([sa]),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "safe_abort_step",
    "∀ n : Num, \{vars}, (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → safe_abort(n,s2,f2,es2,q,a)) → safe_abort(SUC(n),s,f,es,q,a)",
    seq([rw([sa]), @meson.meson_tac(ths([]))]),
  )
  let _ = lemma(
    "safe_abort_after_step",
    "∀ n : Num, \{vars}, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], safe_abort(SUC(n),s,f,es,q,a) && reduce(s,f,es,s2,f2,es2) → safe_abort(n,s2,f2,es2,q,a)",
    seq([
      rw([sa]),
      @meson.meson_tac(
        ths([@wasm.thm("reduce_not_vals"), @wasm.thm("reduce_not_trap")]),
      ),
    ]),
  )
  let cfg = "(Wstore,Wframe,List[Einstr])"
  let _ = lemma(
    "safe_abort_run",
    "∀ c : \{cfg}, ∀ c2 : \{cfg}, reduce_trans(c,c2) → (∀ q : \{assn}, ∀ a : \{at}, (∀ n : Num, safe_abort(n,FST(c),FST(SND(c)),SND(SND(c)),q,a)) → (∀ n : Num, safe_abort(n,FST(c2),FST(SND(c2)),SND(SND(c2)),q,a)))",
    seq([
      @tactics.match_mp_tac(@wasm.thm("reduce_trans_induct")),
      beta_goal(),
      rw([@pair.fst(), @pair.snd()]),
      @tactics.repeat_tac(@tactics.strip_tac),
      @meson.asm_meson_tac(ths([thm("safe_abort_after_step")])),
    ]),
  )
  let _ = lemma(
    "safe_abort_adequate",
    "\{vars}, (∀ n : Num, safe_abort(n,s,f,es,q,a)) → (∃ vs : List[Value], es == MAP(v_to_e,vs) && q(s,f,vs)) || (es == [Trap] && a(s,f)) || (∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2))",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.mp_tac(@bool.spec(tm("SUC(0)"), th))),
      rw([sa]),
      @meson.meson_tac(ths([])),
    ]),
  )
}
