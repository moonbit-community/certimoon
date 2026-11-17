// Native calls with one argument and one result, when the body falls through
// or deliberately aborts. Early returns are covered separately by ordinary specs.

///|
fn prove_abort_value_call() -> Unit raise {
  let at = "(Wstore,Wframe) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let inst = (th : @kernel.Thm, xs : Array[String]) => {
    @bool.ispecl(@list.List(xs.map(tm)), th)
  }
  let sf = ["(s : Wstore)", "(f : Wframe)"]
  let addr = "sfunc_ind(f_inst((f : Wframe)),(j : Num))"
  let callee = "Wframe(CONS((arg : Value),(zs : List[Value])),(i : Inst))"
  let content = "[Label(1,NIL,MAP(Basic,(code : List[B_e])))]"
  let frame = "[Frame(1,\{callee},\{content})]"
  let native = "EL(\{addr},s_funcs((s : Wstore))) == Func_native((i : Inst),Tf([T_num(T_i32)],[T_num(T_i32)]),(ts : List[Valtype]),(code : List[B_e])) && n_zeros(ts) == SOME((zs : List[Value]))"
  let normal = [
    @lists.map(),
    @lists.append(),
    @lists.length(),
    @lists.append_nil(),
  ]
  let callcan = @simp.rewrite_rule(ths(normal))(
    inst(thm("call_can_step"), sf + ["[ (arg : Value) ]", "(j : Num)"]),
  )
  let callstep = @simp.rewrite_rule(ths(normal))(
    inst(thm("call_step"), sf + ["[ (arg : Value) ]", "(j : Num)"]),
  )
  let ivargs = sf +
    [
      "(NIL : List[Value])", "[ (arg : Value) ]", addr, "(i : Inst)", "[T_num(T_i32)]",
      "[T_num(T_i32)]", "(ts : List[Valtype])", "(code : List[B_e])", "(zs : List[Value])",
    ]
  let ivcan = @simp.rewrite_rule(ths(normal))(
    inst(thm("invoke_can_step"), ivargs),
  )
  let ivstep = @simp.rewrite_rule(ths(normal))(inst(thm("invoke_step"), ivargs))
  let ivcan = @equal.conv_rule(@calc_num.num_reduce_conv, ivcan)
  let ivstep = @equal.conv_rule(@calc_num.num_reduce_conv, ivstep)
  let vars = "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ arg : Value, ∀ j : Num, ∀ i : Inst, ∀ ts : List[Valtype], ∀ code : List[B_e], ∀ zs : List[Value], ∀ qin : \{assn}, ∀ ain : \{at}, ∀ q : \{assn}, ∀ a : \{at}"
  let _ = lemma(
    "safe_abort_call_value",
    "\{vars}, (\{native}) && (∀ k : Num, safe_abort(k,s,\{callee},MAP(Basic,code),qin,ain)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ vs : List[Value], qin(s2,f2,vs) → q(s2,f,vs)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ain(s2,f2) → a(s2,f)) → safe_abort(n,s,f,APPEND(MAP(v_to_e,[arg]),[Basic(Call(j))]),q,a)",
    seq([
      gen,
      strip,
      rw(normal),
      @tactics.match_mp_tac(thm("safe_abort_deterministic_step")),
      @tactics.exists_tac(tm("(s : Wstore)")),
      @tactics.exists_tac(tm("(f : Wframe)")),
      @tactics.exists_tac(
        tm("APPEND(MAP(v_to_e,[(arg : Value)]),[Invoke(\{addr})])"),
      ),
      rw(normal),
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
              rw(normal),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(seq([@tactics.match_mp_tac(ivcan), arw(normal)])),
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
