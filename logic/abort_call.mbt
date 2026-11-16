// Unit native calls: enter the native frame, then propagate its two outcomes.

///|
fn prove_abort_unit_call() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let inst = (th : @kernel.Thm, xs : Array[String]) => {
    @bool.ispecl(@list.List(xs.map(tm)), th)
  }
  let _ = lemma(
    "safe_abort_deterministic_step",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], ∀ q : \{assn}, ∀ a : \{at}, reduce(s,f,es,s2,f2,es2) && (∀ t1 : Wstore, ∀ t2 : Wframe, ∀ t3 : List[Einstr], reduce(s,f,es,t1,t2,t3) → t1 == s2 && t2 == f2 && t3 == es2) && (∀ k : Num, safe_abort(k,s2,f2,es2,q,a)) → safe_abort(n,s,f,es,q,a)",
    seq([
      gen,
      strip,
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @tactics.first(
        @list.List([
          solve(rw([thm("safe_abort")])),
          solve(
            seq([
              @tactics.match_mp_tac(thm("safe_abort_step")),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.exists_tac(tm("(s2 : Wstore)")),
                    @tactics.exists_tac(tm("(f2 : Wframe)")),
                    @tactics.exists_tac(tm("(es2 : List[Einstr])")),
                    arw([]),
                  ]),
                  seq([
                    @tactics.x_gen_tac(tm("(t1 : Wstore)")),
                    @tactics.x_gen_tac(tm("(t2 : Wframe)")),
                    @tactics.x_gen_tac(tm("(t3 : List[Einstr])")),
                    @tactics.disch_tac,
                    @tactics.first_x_assum(th => {
                      @tactics.mp_tac(
                        @bool.ispecl(
                          @list.List(
                            [
                              "(t1 : Wstore)", "(t2 : Wframe)", "(t3 : List[Einstr])",
                            ].map(tm),
                          ),
                          th,
                        ),
                      )
                    }),
                    arw([]),
                    strip,
                    subst_vars(),
                    arw([]),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let sf = ["(s : Wstore)", "(f : Wframe)"]
  let addr = "sfunc_ind(f_inst((f : Wframe)),(j : Num))"
  let callee = "Wframe((zs : List[Value]),(i : Inst))"
  let content = "[Label(0,NIL,MAP(Basic,(code : List[B_e])))]"
  let frame = "[Frame(0,\{callee},\{content})]"
  let native = "EL(\{addr},s_funcs((s : Wstore))) == Func_native((i : Inst),Tf(NIL,NIL),(ts : List[Valtype]),(code : List[B_e])) && n_zeros(ts) == SOME((zs : List[Value]))"
  let normal = [
    @lists.map(),
    @lists.append(),
    @lists.length(),
    @lists.append_nil(),
  ]
  let callcan = @simp.rewrite_rule(ths(normal))(
    inst(thm("call_can_step"), sf + ["(NIL : List[Value])", "(j : Num)"]),
  )
  let callstep = @simp.rewrite_rule(ths(normal))(
    inst(thm("call_step"), sf + ["(NIL : List[Value])", "(j : Num)"]),
  )
  let ivargs = sf +
    [
      "(NIL : List[Value])", "(NIL : List[Value])", addr, "(i : Inst)", "(NIL : List[Valtype])",
      "(NIL : List[Valtype])", "(ts : List[Valtype])", "(code : List[B_e])", "(zs : List[Value])",
    ]
  let ivcan = @simp.rewrite_rule(ths(normal))(
    inst(thm("invoke_can_step"), ivargs),
  )
  let ivstep = @simp.rewrite_rule(ths(normal))(inst(thm("invoke_step"), ivargs))
  let vars = "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ j : Num, ∀ i : Inst, ∀ ts : List[Valtype], ∀ code : List[B_e], ∀ zs : List[Value], ∀ qin : \{assn}, ∀ ain : \{at}, ∀ q : \{assn}, ∀ a : \{at}"
  let _ = lemma(
    "safe_abort_call_unit",
    "\{vars}, (\{native}) && (∀ k : Num, safe_abort(k,s,\{callee},MAP(Basic,code),qin,ain)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qin(s2,f2,vs) → q(s2,f,vs)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ain(s2,f2) → a(s2,f)) → safe_abort(n,s,f,[Basic(Call(j))],q,a)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("safe_abort_deterministic_step")),
      @tactics.exists_tac(tm("(s : Wstore)")),
      @tactics.exists_tac(tm("(f : Wframe)")),
      @tactics.exists_tac(tm("[Invoke(\{addr})]")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@tactics.accept_tac(callcan)),
          solve(@meson.asm_meson_tac(ths([callstep]))),
          solve(
            seq([
              gen,
              @tactics.match_mp_tac(thm("safe_abort_deterministic_step")),
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f : Wframe)")),
              @tactics.exists_tac(tm(frame)),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(seq([@tactics.match_mp_tac(ivcan), arw([])])),
                  solve(@meson.asm_meson_tac(ths([ivstep]))),
                  solve(
                    seq([
                      gen,
                      @tactics.match_mp_tac(thm("safe_abort_frame")),
                      @tactics.exists_tac(tm("(qin : \{assn})")),
                      @tactics.exists_tac(tm("(ain : \{at})")),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          seq([
                            @tactics.match_mp_tac(thm("safe_abort_label")),
                            @meson.asm_meson_tac(ths([])),
                          ]),
                          @meson.asm_meson_tac(ths([])),
                        ]),
                      ),
                    ]),
                  ),
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
