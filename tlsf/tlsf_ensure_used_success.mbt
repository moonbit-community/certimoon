///|
fn prove_tlsf_ensure_used_success() -> Unit raise {
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
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let lim2 = "(lim : Num)+(delta : Num)"
  let zeros = "pts((lim : Num),REPLICATE((delta : Num),(word(0) : Word[8])))"
  let large = "tlsf_large((d : \{w}),(lim : Num),\{m},\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let pre = "st(NIL,[V_num(ConstInt32(\{m})),V_num(ConstInt32((e : \{w})))],(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == \{lim2} && star(\{large},star(\{zeros},(fp : \{rty})(gs,ms)),h))"
  let args = [
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
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
    "(lim : Num)",
    lim2,
  ]
  let append = inst(thm("tlsf_ensure_append"), args)
  let at = args_of(@basics.dest_imp(@kernel.concl(append)).1, "sl_triple_m", 7).unwrap()
  let grow = inst(thm("tlsf_ensure_append_grow"), [
    "(ys : \{lw})",
    "(d : \{w})",
    "(lim : Num)",
    "(delta : Num)",
    m,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})((gs : List[Value]),(ms : Num))",
  ])
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ e : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}, ∀ lim : Num, ∀ delta : Num"
  let cond = "(\{show(@basics.dest_imp(@kernel.concl(append)).0)}) && 24 <= (delta : Num)"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let _ = lemma(
    "tlsf_ensure_used_success",
    "\{vars}, \{cond} → sl_triple_m(fs,tabs,inst,\{pre},\{show(at[4])},\{show(at[5])},NIL)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(at[3]),
      @tactics.exists_tac(at[5]),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(seq([@tactics.match_mp_tac(append), arw([])])),
          solve(
            seq([
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
            ]),
          ),
          solve(seq([gen, beta_goal(), strip, arw([])])),
        ]),
      ),
    ]),
  )
}
