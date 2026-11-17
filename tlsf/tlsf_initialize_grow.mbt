///|
fn prove_tlsf_initialize_grow() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let before = "(before : \{heap})"
  let fp = "(fp : \{rty})"
  let req = "tlsf_initialize_required(\{d})"
  let old = "(word(DIV(\{lim},65536)) : \{w})"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("tlsf_base("+d+")")},\{i(req)},\{i(old)}]"
  let saved = "tlsf_initialize_saved(\{d},\{lim},\{before},\{fp})"
  let fresh = "tlsf_initialize_fresh(\{d},\{lim},\{fp})"
  let abortp = "tlsf_initialize_abort(\{d},\{lim},\{before},\{fp})"
  let good = "st(NIL,\{lc},\{fresh})"
  let bad = "st([\{i("word(4294967295)")}],\{lc},\{saved})"
  let ok = "st([\{i(old)}],\{lc},\{fresh})"
  let valid = "tlsf_initialize_valid(\{d},\{lim})"
  let cond = "word_ugt(\{req},\{old})"
  let envs = [
    "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)",
  ]
  let env = envs.join(",")
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  let guard_code = "APPEND(tlsf_initialize_guard_test(\{d},(push : Num)),[If(Tbv(NONE),[Unreachable],NIL)])"
  let amount = inst(thm("tlsf_initialize_grow_amount_raw"), [
    d,
    "(push : Num)",
    i("tlsf_base(" + d + ")"),
    req,
    old,
    saved,
  ])
  let grow = inst(
    thm("tlsf_initialize_memory_grow"),
    envs + [d, lim, before, fp],
  )
  let gp = args_of(@basics.dest_imp(@kernel.concl(grow)).1, "sl_triple_m", 7).unwrap()
  let failure = inst(
    thm("tlsf_initialize_guard_abort"),
    envs + [d, "(push : Num)", lc, saved, good, abortp],
  )
  let success = inst(
    thm("tlsf_initialize_guard_continue"),
    envs + [d, "(push : Num)", lc, fresh, good, abortp, old],
  )
  let orrule = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("sl_abort_or_m"), envs + [bad, ok, guard_code, good, abortp]),
  )
  let _ = lemma(
    "tlsf_initialize_grow_yes_saved",
    "\{vars}, \{valid} && \{cond} → sl_abort_m(\{env},st(NIL,\{lc},\{saved}),tlsf_initialize_grow_yes(d,push),\{good},\{abortp})",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "(lim : Num) <= 4294967296",
          seq([
            @tactics.undisch_tac(tm(valid)),
            rw([thm("tlsf_initialize_valid")]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        free_have(
          "!(\{old} == word(4294967295))",
          seq([
            @tactics.match_mp_tac(thm("tlsf_page_result_not_failure")),
            arw([]),
          ]),
        ),
        rw([thm("tlsf_initialize_grow_yes_parts")]),
        @tactics.match_mp_tac(thm("sl_abort_seq_m")),
        @tactics.exists_tac(gp[3]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_abort_conseq(amount, same_tac(), same_tac()),
            seq([
              @tactics.match_mp_tac(thm("sl_abort_seq_m")),
              @tactics.exists_tac(gp[5]),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  initialize_abort_conseq(grow, same_tac(), same_tac()),
                  seq([
                    rw([@class.eta_ax()]),
                    @tactics.match_mp_tac(orrule),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([
                          @tactics.match_mp_tac(failure),
                          rw([
                            thm("st"),
                            thm("tlsf_initialize_saved"),
                            thm("tlsf_initialize_abort"),
                          ]),
                          @meson.meson_tac(ths([])),
                        ]),
                        free_apply(success),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_initialize_no_growth_fresh",
    "∀ d : \{w}, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{valid} && !\{cond} → \{saved}(gs,ms,h) → \{fresh}(gs,ms,h)",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_initialize_limit_cases"), [d, lim])),
        arw([]),
        @tactics.disch_tac,
        rw([thm("tlsf_initialize_saved"), thm("tlsf_initialize_fresh")]),
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        arw([]),
      ])
    },
  )
  let grow_test = inst(thm("tlsf_initialize_grow_test_raw"), [
    d,
    "(push : Num)",
    i("tlsf_base(" + d + ")"),
    req,
    old,
    saved,
  ])
  let gt = args_of(@kernel.concl(grow_test), "sl_triple", 3).unwrap()
  let nil = inst(
    thm("sl_abort_nil_m"),
    envs + ["st(NIL,\{lc},\{saved})", abortp],
  )
  let _ = lemma(
    "tlsf_initialize_grow_saved",
    "\{vars}, \{valid} → sl_abort_m(\{env},st(NIL,\{lc},\{saved}),tlsf_initialize_grow(d,push),\{good},\{abortp})",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_initialize_grow_parts")]),
        @tactics.match_mp_tac(thm("sl_abort_seq_m")),
        @tactics.exists_tac(gt[2]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_abort_conseq(grow_test, same_tac(), same_tac()),
            seq([
              @tactics.match_mp_tac(thm("sl_abort_if_st_m")),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.disch_tac,
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(ths([thm("wasm_bool_zero")])),
                    ),
                    seq([
                      @tactics.match_mp_tac(
                        thm("tlsf_initialize_grow_yes_saved"),
                      ),
                      arw([]),
                    ]),
                  ]),
                  seq([
                    @tactics.disch_tac,
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(ths([thm("wasm_bool_zero")])),
                    ),
                    initialize_abort_conseq(
                      nil,
                      same_tac(),
                      seq([
                        gen,
                        rw([thm("st")]),
                        strip,
                        arw([]),
                        @tactics.mp_tac(
                          inst(thm("tlsf_initialize_no_growth_fresh"), [
                            d,
                            lim,
                            before,
                            fp,
                            "(gs : List[Value])",
                            "(ms : Num)",
                            "(h : \{heap})",
                          ]),
                        ),
                        arw([]),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
