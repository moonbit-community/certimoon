///|
fn prove_tlsf_ensure_focus_body() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let d = "(d : \{w})"
  let top = "(top : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "(xs : \{lw})"
  let params = [
    d,
    "(s : \{w})",
    "(lim : Num)",
    top,
    xs,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  let q = "tlsf_ensure_post(\{params.join(",")})"
  let rp = body_post(q)
  let large = "tlsf_large(\{d},(lim : Num),\{top},\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let pre = "st(NIL,[\{i("s")},\{i("word(0)")}],(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && h == (before : \{heap}) && star(\{large},(fp : \{rty})(gs,lim),h))"
  let phy = "tlsf_physical_ok(\{d},(lim : Num),\{top},\{xs},\{hd})"
  let facts = "\{phy} && tlsf_bins_match(\{xs},\{hd},(bl : \{bt})) && tlsf_tables_sync((fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let popnative = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code(\{d}))"
  let pushnative = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(\{d}))"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ s : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let source = inst(thm("tlsf_ensure_body_snoc"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    d,
    "(pop : Num)",
    "(push : Num)",
    "(ys : \{lw})",
    top,
    "(s : \{w})",
    "(lim : Num)",
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ])
  let source = @simp.rewrite_rule(
    ths([thm("tlsf_ensure_saved"), @class.eta_ax()]),
  )(source)
  let _ = lemma(
    "tlsf_ensure_body_focused",
    "\{vars}, 16 <= val((s : \{w})) && val(s) <= 4160749568 && \{popnative} && \{pushnative} && \{facts} → sl_triple_g(G,fs,tabs,inst,\{rp},\{pre},tlsf_ensure_code(d,pop,push),\{rp},[\{rp}])",
    () => {
      seq([
        gen,
        strip,
        arw([@class.eta_ax()]),
        @tactics.mp_tac(
          inst(thm("tlsf_physical_last"), [d, "(lim : Num)", top, xs, hd]),
        ),
        arw([]),
        @tactics.disch_then(
          @tactics.x_choose_then(tm("(ys : \{lw})"))(th => {
            @tactics.assume_tac(th)
          }),
        ),
        subst_vars(),
        @tactics.match_mp_tac(source),
        arw([]),
      ])
    },
  )
}
