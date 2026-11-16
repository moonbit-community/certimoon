///|
fn prove_tlsf_initialize_check() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let ev = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let sn = "st(NIL,(lc : List[Value]),(R : \{rty}))"
  let enta = "∀ vs : List[Value], ∀ lc2 : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{sn}(vs,lc2,gs,ms,h) → (A : \{sassn})(vs,lc2,gs,ms,h)"
  let _ = lemma(
    "tlsf_initialize_abort_if",
    "\{ev}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ A : \{sassn}, ∀ c : \{w}, (\{enta}) → sl_abort_m(\{env},st([\{i("c")}],lc,R),[If(Tbv(NONE),[Unreachable],NIL)],\{sn},A)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_abort_if_st_m")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.disch_tac,
            @tactics.match_mp_tac(thm("sl_abort_unreachable_m")),
            arw([]),
          ]),
          seq([
            @tactics.disch_tac,
            @tactics.match_accept_tac(thm("sl_abort_nil_m")),
          ]),
        ]),
      ),
    ]),
  )
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let fp = "(fp : \{rty})"
  let before = "(before : \{heap})"
  let saved = "tlsf_initialize_saved(\{d},\{lim},\{before},\{fp})"
  let abortp = "tlsf_initialize_abort(\{d},\{lim},\{before},\{fp})"
  let base = "tlsf_base(\{d})"
  let req = "tlsf_initialize_required(\{d})"
  let old = "(word(DIV(\{lim},65536)) : \{w})"
  let lc0 = "[\{i(base)},\{i(req)},(l2 : Value)]"
  let lc = "[\{i(base)},\{i(req)},\{i(old)}]"
  let size = inst(thm("st_memory_size_at"), [
    "(NIL : List[Value])", lc0, lim, saved,
  ])
  let size = @bool.mp(
    size,
    @tactics.prove(
      @basics.dest_imp(@kernel.concl(size)).0,
      seq([rw([thm("tlsf_initialize_saved")]), @meson.meson_tac(ths([]))]),
    ),
  )
  let rt = args_of(@kernel.concl(size), "sl_triple", 3).unwrap()
  let check_test = inst(thm("tlsf_initialize_check_test_raw"), [
    d,
    "(push : Num)",
    i(base),
    req,
    old,
    saved,
    "(l2 : Value)",
  ])
  let tt = args_of(@kernel.concl(check_test), "sl_triple", 3).unwrap()
  let _ = lemma(
    "tlsf_initialize_check_saved",
    "\{ev}, ∀ d : \{w}, ∀ push : Num, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ l2 : Value, sl_abort_m(\{env},st(NIL,\{lc0},\{saved}),tlsf_initialize_check(d,push),st(NIL,\{lc},\{saved}),\{abortp})",
    seq([
      gen,
      rw([thm("tlsf_initialize_check_parts")]),
      @tactics.match_mp_tac(thm("sl_abort_seq_m")),
      @tactics.exists_tac(rt[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          initialize_abort_conseq(size, same_tac(), same_tac()),
          seq([
            @tactics.match_mp_tac(thm("sl_abort_seq_m")),
            @tactics.exists_tac(tt[2]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                initialize_abort_conseq(check_test, same_tac(), same_tac()),
                seq([
                  @tactics.match_mp_tac(thm("tlsf_initialize_abort_if")),
                  rw([
                    thm("st"),
                    thm("tlsf_initialize_saved"),
                    thm("tlsf_initialize_abort"),
                  ]),
                  @meson.meson_tac(ths([])),
                ]),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
}
