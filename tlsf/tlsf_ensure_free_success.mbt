///|
fn prove_tlsf_ensure_free_success() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let rest = "APPEND((us : \{lw}),(bs : \{lw}))"
  let lim2 = "(lim : Num)+(delta : Num)"
  let zeros = "pts((lim : Num),REPLICATE((delta : Num),(word(0) : Word[8])))"
  let frame = "(gs : List[Value]) => (ms : Num) => star(\{zeros},(fp : \{rty})(gs,ms))"
  let nfl = "tlsf_pop_fl(\{h},(fl : \{w}),(sb : (Num) -> \{w}),\{rest})"
  let nsb = "tlsf_pop_sb(\{h},(sb : (Num) -> \{w}),\{rest})"
  let nbl = "tlsf_pop_bl(\{h},(bl : \{bt}),\{rest})"
  let pop = inst(thm("tlsf_ensure_pop_detach"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(pop : Num)",
    "(ys : \{lw})",
    "(NIL : \{lw})",
    m,
    "(e : \{w})",
    "(lim : Num)",
    lim2,
    m,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(us : \{lw})",
    "(bs : \{lw})",
    frame,
  ])
  let pt = args_of(@basics.dest_imp(@kernel.concl(pop)).1, "sl_triple_m", 7).unwrap()
  let resize = inst(thm("tlsf_ensure_resize"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(ys : \{lw})",
    m,
    "(e : \{w})",
    hd,
    nfl,
    nsb,
    nbl,
    "(fp : \{rty})",
    "(lim : Num)",
    lim2,
  ])
  let rt = args_of(@basics.dest_imp(@kernel.concl(resize)).1, "sl_triple_m", 7).unwrap()
  let grow = inst(thm("tlsf_ensure_detached_grow"), [
    "(ys : \{lw})",
    "(d : \{w})",
    "(lim : Num)",
    "(delta : Num)",
    m,
    hd,
    nfl,
    nsb,
    nbl,
    "(fp : \{rty})((gs : List[Value]),(ms : Num))",
  ])
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ e : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ bs : \{lw}, ∀ fp : \{rty}, ∀ lim : Num, ∀ delta : Num"
  let nativepush = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let cond = "(\{show(@basics.dest_imp(@kernel.concl(pop)).0)}) && \{nativepush} && \{lim2} <= 4294967296 && MOD(\{lim2},65536) == 0"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let pre = seq([
    gen,
    rw([thm("st")] + lift_rws()),
    strip,
    arw([]),
    @tactics.mp_tac(grow),
    arw([]),
    @tactics.disch_then(th => {
      @tactics.assume_tac(@bool.spec(tm("(h : \{heap})"), th))
    }),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths(ac))),
    arw(ac),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "tlsf_ensure_free_success",
    "\{vars}, \{cond} → sl_triple_m(fs,tabs,inst,\{show(pt[3])},APPEND(\{show(pt[4])},\{show(rt[4])}),\{show(rt[5])},NIL)",
    () => {
      seq([
        gen,
        strip,
        have(
          "tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{m}),\{nbl})",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_pop_bins_match"), [
                xs,
                hd,
                "(bl : \{bt})",
                m,
                "(us : \{lw})",
                "(bs : \{lw})",
              ]),
            ),
            arw([@lists.mem_append(), @lists.mem()]),
          ]),
        ),
        @tactics.match_mp_tac(thm("sl_seq_m")),
        @tactics.exists_tac(pt[5]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([@tactics.match_mp_tac(pop), arw([])]),
            seq([
              @tactics.match_mp_tac(thm("sl_conseq_m")),
              @tactics.exists_tac(rt[3]),
              @tactics.exists_tac(rt[5]),
              rw([]),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      @tactics.match_mp_tac(resize),
                      arw([]),
                      @int.asm_arith_tac,
                    ]),
                  ),
                  solve(pre),
                  solve(seq([gen, beta_goal(), strip, arw([])])),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
