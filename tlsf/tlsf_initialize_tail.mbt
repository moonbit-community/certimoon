// Establish the complete invariant after the checks and optional growth.

///|
fn prove_tlsf_initialize_tail() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let before = "(before : \{heap})"
  let fp = "(fp : \{rty})"
  let newlim = "tlsf_initialize_limit(\{d},\{lim})"
  let frozen = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{fp}(gs,\{lim},h)"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let req = "tlsf_initialize_required(\{d})"
  let old = "(word(DIV(\{lim},65536)) : \{w})"
  let lc = "[\{i("tlsf_base("+d+")")},\{i(req)},\{i(old)}]"
  let fresh = "tlsf_initialize_fresh(\{d},\{lim},\{fp})"
  let post = "tlsf_initialize_post(\{d},\{lim},\{before},\{fp})"
  let abortp = "tlsf_initialize_abort(\{d},\{lim},\{before},\{fp})"
  let envs = [
    "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)",
  ]
  let env = envs.join(",")
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(\{d}))"
  let work = inst(
    thm("tlsf_initialize_tail_work"),
    envs + [d, "(push : Num)", newlim, i(req), i(old), frozen],
  )
  let close = inst(thm("tlsf_initialize_work_close"), [d, newlim, frozen])
  let _ = lemma(
    "tlsf_initialize_tail_fresh",
    "\{vars}, tlsf_initialize_valid(d,lim) && \{native} → sl_abort_m(\{env},st(NIL,\{lc},\{fresh}),tlsf_initialize_tail(d,push),\{body_post(post)},\{abortp})",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_limit_bounds"), [d, lim])),
      arw([]),
      strip,
      @tactics.undisch_tac(tm("tlsf_initialize_valid(\{d},\{lim})")),
      rw([thm("tlsf_initialize_valid")]),
      strip,
      initialize_abort_conseq(
        work,
        seq([
          gen,
          rw([thm("st"), thm("tlsf_initialize_fresh")]),
          strip,
          subst_vars(),
          arw([]),
          @tactics.mp_tac(
            inst(thm("tlsf_initialize_zero_ready"), [
              d,
              newlim,
              frozen,
              "(gs : List[Value])",
              newlim,
              "(h : \{heap})",
            ]),
          ),
          arw([@class.eta_ax()]),
        ]),
        seq([
          gen,
          beta_goal(),
          rw([thm("st"), thm("tlsf_initialize_post")]),
          strip,
          subst_vars(),
          arw([]),
          @tactics.mp_tac(close),
          arw([@class.eta_ax()]),
          @tactics.disch_tac,
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "tlsf_initialize_work" {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          arw([@class.eta_ax()]),
          @tactics.repeat_tac(@tactics.strip_tac),
          subst_vars(),
          arw([]),
        ]),
      ),
    ]),
  )
}
