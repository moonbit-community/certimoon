// The shipped unit function: no arguments or results and three zero locals.

///|
fn prove_tlsf_initialize_module() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w32})"
  let lim = "(lim : Num)"
  let before = "(before : \{heap})"
  let fp = "(fp : \{rty})"
  let envs = [
    "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)",
  ]
  let env = envs.join(",")
  let args = "\{d},\{lim},\{before},\{fp}"
  let p = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => tlsf_initialize_pre(\{args},NIL,gs,ms,h)"
  let q = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => tlsf_initialize_post(\{args},NIL,gs,ms,h)"
  let a = "tlsf_initialize_saved(\{args})"
  let ap = "tlsf_initialize_abort(\{args})"
  let zero = "V_num(ConstInt32((word(0) : \{w32})))"
  let zs = "[\{zero},\{zero},\{zero}]"
  let ts = "[T_num(T_i32),T_num(T_i32),T_num(T_i32)]"
  let code = "tlsf_initialize_code(\{d},(push : Num))"
  let native = "EL(sfunc_ind((inst : Inst),(j : Num)),(fs : List[Cl])) == Func_native(inst,Tf(NIL,NIL),\{ts},\{code})"
  let push = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),\{ts},tlsf_push_code(\{d}))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w32}, ∀ j : Num, ∀ push : Num, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ lc0 : List[Value]"
  let body = inst(
    thm("tlsf_initialize_body"),
    envs + [d, "(push : Num)", lim, before, fp],
  )
  let rule = inst(
    thm("sl_abort_call_unit_m"),
    envs + ["(j : Num)", ts, code, zs, "(lc0 : List[Value])", p, q, a],
  )
  let _ = lemma(
    "tlsf_initialize_all",
    "\{vars}, tlsf_initialize_valid(d,lim) && \{native} && \{push} → sl_abort_m(\{env},st(NIL,lc0,\{p}),[Call(j)],st(NIL,lc0,\{q}),\{ap})",
    seq([
      gen,
      strip,
      rw([
        thm("tlsf_initialize_saved"),
        thm("tlsf_initialize_abort"),
        @class.eta_ax(),
      ]),
      @tactics.match_mp_tac(
        @simp.rewrite_rule(
          ths([
            thm("tlsf_initialize_saved"),
            thm("tlsf_initialize_abort"),
            @class.eta_ax(),
          ]),
        )(rule),
      ),
      arw([
        @wasm.thm("n_zeros"),
        @wasm.thm("bitzero"),
        @wasm.thm("bitzero_num"),
        @wasm.thm("map_option"),
        @wasm.thm("those"),
        @lists.map(),
        thm("tlsf_initialize_saved"),
        thm("tlsf_initialize_abort"),
      ]),
      initialize_abort_conseq(
        body,
        same_tac(),
        seq([
          gen,
          beta_goal(),
          rw([thm("tlsf_initialize_post")]),
          @meson.meson_tac(ths([])),
        ]),
        on_abort=seq([
          gen,
          beta_goal(),
          rw([thm("tlsf_initialize_saved"), thm("tlsf_initialize_abort")]),
        ]),
      ),
    ]),
  )
  let cp = "st(NIL,(lc0 : List[Value]),\{p})"
  let cq = "st(NIL,(lc0 : List[Value]),\{q})"
  let keep = (
    assertion : String,
    state : String,
    frame : String,
    values : String,
  ) => {
    "keep(\{env},lift(\{assertion},(fr : \{hprop})),\{state},\{frame},\{values})"
  }
  let step = "reduce_trans(((s : Wstore),(f : Wframe),APPEND(MAP(v_to_e,(vs : List[Value])),[Basic(Call((j : Num)))])),((s2 : Wstore),(f2 : Wframe),(es2 : List[Einstr])))"
  let outcome = "(∃ res : List[Value], es2 == MAP(v_to_e,res) && \{keep(cq,"(s2 : Wstore)","(f2 : Wframe)","res")}) || (es2 == [Trap] && \{keep(ap,"(s2 : Wstore)","(f2 : Wframe)","NIL")}) || (∃ s3 : Wstore, ∃ f3 : Wframe, ∃ es3 : List[Einstr], reduce(s2,f2,es2,s3,f3,es3))"
  let run = inst(
    thm("sl_abort_m_adequate"),
    envs +
    [
      cp,
      "[Call((j : Num))]",
      cq,
      ap,
      "(fr : \{hprop})",
      "(s : Wstore)",
      "(f : Wframe)",
      "(vs : List[Value])",
      "(s2 : Wstore)",
      "(f2 : Wframe)",
      "(es2 : List[Einstr])",
    ],
  )
  let _ = lemma(
    "tlsf_initialize_run",
    "\{vars}, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], tlsf_initialize_valid(d,lim) && \{native} && \{push} && \{keep(cp,"(s : Wstore)","(f : Wframe)","(vs : List[Value])")} && \{step} → \{outcome}",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(
          thm("tlsf_initialize_all"),
          envs +
          [
            d, "(j : Num)", "(push : Num)", lim, before, fp, "(lc0 : List[Value])",
          ],
        ),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(run),
      arw([@class.eta_ax(), @lists.map()]),
    ]),
  )
}
