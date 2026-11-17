// The emitted -1 test either continues, or aborts with the old heap intact.

///|
fn prove_tlsf_initialize_guard() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ lc : List[Value], ∀ R : \{rty}, ∀ Q : \{sassn}, ∀ A : \{sassn}"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let code = "APPEND(tlsf_initialize_guard_test((d : \{w}),(push : Num)),[If(Tbv(NONE),[Unreachable],NIL)])"
  let state = "st(NIL,(lc : List[Value]),(R : \{rty}))"
  let a = "(A : \{sassn})"
  let raw = (ret : String) => {
    inst(thm("tlsf_initialize_guard_test_raw"), [
      "(d : \{w})",
      "(push : Num)",
      "(lc : List[Value])",
      ret,
      "(R : \{rty})",
    ])
  }
  let mid = (ret : String) => {
    "st([\{i("wasm_bool(("+ret+" : "+w+") == word(4294967295))")}],(lc : List[Value]),(R : \{rty}))"
  }
  let ent = "∀ vs : List[Value], ∀ lc2 : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{state}(vs,lc2,gs,ms,h) → \{a}(vs,lc2,gs,ms,h)"
  let _ = lemma(
    "tlsf_initialize_guard_abort",
    "\{vars}, (\{ent}) → sl_abort_m(\{env},st([\{i("word(4294967295)")}],lc,R),\{code},Q,A)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.match_mp_tac(thm("sl_abort_seq_m")),
        @tactics.exists_tac(tm(mid("word(4294967295)"))),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_abort_conseq(
              raw("(word(4294967295) : \{w})"),
              same_tac(),
              same_tac(),
            ),
            seq([
              @tactics.match_mp_tac(thm("sl_abort_if_st_m")),
              rw([thm("wasm_bool_zero")]),
              @tactics.match_mp_tac(thm("sl_abort_unreachable_m")),
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_initialize_guard_continue",
    "\{vars}, ∀ ret : \{w}, !(ret == word(4294967295)) → sl_abort_m(\{env},st([\{i("ret")}],lc,R),\{code},\{state},A)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have(
          "(wasm_bool((ret : \{w}) == word(4294967295)) : \{w}) == word(0)",
          arw([thm("wasm_bool_zero")]),
        ),
        @tactics.match_mp_tac(thm("sl_abort_seq_m")),
        @tactics.exists_tac(tm(mid("ret"))),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_abort_conseq(raw("(ret : \{w})"), same_tac(), same_tac()),
            seq([
              @tactics.match_mp_tac(thm("sl_abort_if_st_m")),
              arw([]),
              @tactics.match_accept_tac(thm("sl_abort_nil_m")),
            ]),
          ]),
        ),
      ])
    },
  )
}
