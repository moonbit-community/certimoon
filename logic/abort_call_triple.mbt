// Native unit calls retain the caller's locals on both outcomes.

///|
fn prove_abort_call_triple() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let bp = "st(NIL,(zs : List[Value]),(P : \{rty}))"
  let bq = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && (Q : \{rty})(gs,ms,h)"
  let ba = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (A : \{rty})(gs,ms,h)"
  let cp = "st(NIL,(lc0 : List[Value]),(P : \{rty}))"
  let cq = "st(NIL,(lc0 : List[Value]),(Q : \{rty}))"
  let kin = "keep(\{env},lift(\{bq},(fr : \{hprop})))"
  let ain = "(s : Wstore) => (f : Wframe) => keep(\{env},lift(\{ba},(fr : \{hprop})),s,f,NIL)"
  let frame = "Wframe((zs : List[Value]),(inst : Inst))"
  let facts = [
    @wasm.thm("f_inst"),
    @wasm.thm("f_locs"),
    thm("gvals"),
    thm("globs_ok"),
  ]
  let _ = lemma(
    "sl_abort_call_unit_m",
    "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ j : Num, ∀ ts : List[Valtype], ∀ code : List[B_e], ∀ zs : List[Value], ∀ lc0 : List[Value], ∀ P : \{rty}, ∀ Q : \{rty}, ∀ A : \{rty}, EL(sfunc_ind(inst,j),fs) == Func_native(inst,Tf(NIL,NIL),ts,code) && n_zeros(ts) == SOME(zs) && sl_abort_m(\{env},\{bp},code,\{bq},\{ba}) → sl_abort_m(\{env},\{cp},[Call(j)],\{cq},\{ba})",
    seq([
      gen,
      strip,
      rw([thm("sl_abort_m")]),
      gen,
      strip,
      have(
        "(vs : List[Value]) == NIL",
        @meson.asm_meson_tac(ths([thm("abort_keep_st_values")])),
      ),
      subst_vars(),
      rw([@lists.map(), @lists.append()]),
      @tactics.match_mp_tac(thm("safe_abort_call_unit")),
      @tactics.exists_tac(tm("(inst : Inst)")),
      @tactics.exists_tac(tm("(ts : List[Valtype])")),
      @tactics.exists_tac(tm("(code : List[B_e])")),
      @tactics.exists_tac(tm("(zs : List[Value])")),
      @tactics.exists_tac(tm(kin)),
      @tactics.exists_tac(tm(ain)),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths(
            [thm("keep"), thm("abort_st_heap"), thm("gvals"), thm("globs_ok")] +
            lift_facts(),
          ),
        ),
      ),
      @tactics.repeat_tac(
        @tactics.first_x_assum(th => {
          if @basics.is_conj(@kernel.concl(th)) {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
      ),
      rw_inst("f"),
      arw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              gen,
              rw(
                [thm("keep"), thm("abort_st_heap")] +
                lift_facts() +
                facts +
                [@lists.map(), @lists.append()],
              ),
              @tactics.first_x_assum(th => {
                if show(@kernel.concl(th)).contains("sl_abort_m") {
                  let point = @bool.ispecl(
                    @list.List(
                      [
                        "(fr : \{hprop})",
                        "(s : Wstore)",
                        frame,
                        "(NIL : List[Value])",
                        "(k : Num)",
                      ].map(tm),
                    ),
                    @simp.rewrite_rule(ths([thm("sl_abort_m")]))(th),
                  )
                  let point = @simp.rewrite_rule(
                    ths(
                      [thm("keep"), thm("abort_st_heap")] +
                      lift_facts() +
                      facts +
                      [@lists.map(), @lists.append()],
                    ),
                  )(point)
                  seq([@tactics.match_mp_tac(point)])
                } else {
                  @tactics.no_tac
                }
              }),
              arw([]),
              @tactics.exists_tac(tm("(j' : Num)")),
              arw([]),
            ]),
          ),
          solve(
            seq([
              gen,
              beta_goal(),
              rw([thm("keep"), thm("abort_st_heap")] + lift_facts() + facts),
              strip,
              rw_inst("f2"),
              arw([]),
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
