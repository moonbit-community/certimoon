// Return- and branch-aware safety with a specified abort. Startup may abort
// inside an allocation attempt, before a later return or block exit.

///|
#callsite(autofill(loc))
fn startup_lemma(
  name : String,
  statement : String,
  tactic : @tactics.Tactic,
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  lemma(name, statement, () => tactic, loc~)
}

///|
fn define_tlsf_start_safety() -> Unit raise {
  let a = @logic.assn
  let ab = "(Wstore,Wframe) -> Bool"
  def(
    "tlsf_safer_abort",
    "tlsf_safer_abort(0,(s : Wstore),(f : Wframe),(es : List[Einstr]),(q : " +
    a +
    "),(l : List[" +
    a +
    "]),(rq : " +
    a +
    "),(ab : " +
    ab +
    ")) == T && " +
    "tlsf_safer_abort(SUC(n),s,f,es,q,l,rq,ab) == (" +
    "(∃ vs : List[Value], es == MAP(v_to_e,vs) && q(s,f,vs)) || " +
    "(∃ i : Num, ∃ vs : List[Value], ∃ lh : Lholed, i < LENGTH(l) && es == lfill(lh,APPEND(MAP(v_to_e,vs),[Basic(Br(i+lh_depth(lh)))])) && EL(i,l,s,f,vs) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → tlsf_safer_abort(n,s2,f2,es2,q,l,rq,ab))) || " +
    "(∃ vs : List[Value], ∃ lh : Lholed, es == lfill(lh,APPEND(MAP(v_to_e,vs),[Basic(Return)])) && rq(s,f,vs)) || " +
    "(es == [Trap] && ab(s,f)) || " +
    "((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → tlsf_safer_abort(n,s2,f2,es2,q,l,rq,ab))))",
  )
}

///|
fn startup_steps(
  exists : @tactics.Tactic,
  each : @tactics.Tactic,
) -> @tactics.Tactic {
  seq([
    @tactics.disj2_tac,
    @tactics.disj2_tac,
    @tactics.disj2_tac,
    @tactics.disj2_tac,
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([exists, seq([@tactics.repeat_tac(@tactics.strip_tac), each])]),
    ),
  ])
}

///|
fn prove_tlsf_start_safety() -> Unit raise {
  let a = @logic.assn
  let ab = "(Wstore,Wframe) -> Bool"
  let vars = "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : " +
    a +
    ", ∀ l : List[" +
    a +
    "], ∀ rq : " +
    a +
    ", ∀ ab : " +
    ab +
    ", "
  let sa = thm("tlsf_safer_abort")
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let strip = @tactics.repeat_tac(@tactics.strip_tac)
  let _ = startup_lemma(
    "tlsf_safer_abort_of_safer",
    "∀ n : Num, " +
    vars +
    "safer(n,s,f,es,q,l,rq) → tlsf_safer_abort(n,s,f,es,q,l,rq,ab)",
    seq([
      @nums.induct_tac,
      rw([sa, thm("safer")]),
      strip,
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_of_abort",
    "∀ n : Num, " +
    vars +
    "safe_abort(n,s,f,es,q,ab) → tlsf_safer_abort(n,s,f,es,q,l,rq,ab)",
    seq([
      @nums.induct_tac,
      rw([sa, thm("safe_abort")]),
      strip,
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_vals",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : " +
    a +
    ", ∀ l : List[" +
    a +
    "], ∀ rq : " +
    a +
    ", ∀ ab : " +
    ab +
    ", q(s,f,vs) → tlsf_safer_abort(n,s,f,MAP(v_to_e,vs),q,l,rq,ab)",
    seq([
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_of_safer")),
      @tactics.match_mp_tac(thm("safer_vals")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_step",
    "∀ n : Num, " +
    vars +
    "(∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → tlsf_safer_abort(n,s2,f2,es2,q,l,rq,ab)) → tlsf_safer_abort(SUC(n),s,f,es,q,l,rq,ab)",
    seq([rw([sa]), @meson.meson_tac(ths([]))]),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_after_step",
    "∀ n : Num, " +
    vars +
    "∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], tlsf_safer_abort(SUC(n),s,f,es,q,l,rq,ab) && reduce(s,f,es,s2,f2,es2) → tlsf_safer_abort(n,s2,f2,es2,q,l,rq,ab)",
    seq([
      rw([sa]),
      @meson.meson_tac(
        ths([
          @wasm.thm("reduce_not_vals"),
          @wasm.thm("reduce_not_trap"),
          thm("return_stuck"),
        ]),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_start_literal_trap",
    "trap_top([Trap])",
    seq([
      rw([@wasm.thm("trap_top")]),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.exists_tac(tm("(NIL : List[Einstr])")),
      rw([@lists.map(), @lists.append()]),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_safer_abort_top_trap",
    "∀ n : Num, " +
    vars +
    "trap_top(es) && ab(s,f) → tlsf_safer_abort(n,s,f,es,q,l,rq,ab)",
    seq([
      strip,
      @tactics.match_mp_tac(thm("tlsf_safer_abort_of_abort")),
      @tactics.match_mp_tac(thm("safe_abort_top_trap")),
      @simp.asm_rewrite_tac(ths([])),
    ]),
  )
  let ctor = @ind_types.distinctness("einstr")
  let _ = startup_lemma(
    "tlsf_safer_abort_trap_assert",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : " +
    a +
    ", ∀ l : List[" +
    a +
    "], ∀ rq : " +
    a +
    ", ∀ ab : " +
    ab +
    ", tlsf_safer_abort(SUC(n),s,f,[Trap],q,l,rq,ab) → ab(s,f)",
    seq([
      rw([
        sa,
        @wasm.thm("reduce_not_trap"),
        @wasm.thm("map_v_to_e_cons"),
        @wasm.thm("eq_v_to_e"),
        ctor,
        @equal.gsym(ctor),
      ]),
      strip,
      @tactics.orelse_tac(
        solve(@simp.asm_rewrite_tac(ths([]))),
        seq([
          @tactics.first_x_assum(th => {
            @tactics.mp_tac(
              @drule.match_mp(@wasm.thm("lfill_trap"))(@equal.gsym(th)),
            )
          }),
          rw([
            thm("snoc_eq"),
            @lists.append_eq_nil(),
            @lists.not_cons_nil(),
            @lists.last(),
            ctor,
            @equal.gsym(ctor),
          ]),
        ]),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_start_br_no_top_trap",
    "∀ lh : Lholed, ∀ vs : List[Value], ∀ i : Num, !trap_top(lfill(lh,APPEND(MAP(v_to_e,vs),[Basic(Br(i+lh_depth(lh)))])))",
    seq([
      strip,
      have("lh_depth((lh : Lholed)) <= (i : Num)+lh_depth(lh)", @int.arith_tac),
      startup_meson(
        ths([thm("br_stuck"), thm("trap_step"), thm("br_not_trap")]),
      ),
    ]),
  )
}
