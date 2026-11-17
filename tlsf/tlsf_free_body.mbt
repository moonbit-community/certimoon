///|
fn prove_tlsf_free_body_focused() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let params = "(d : \{w}),(m : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(fp : \{rty})"
  let q = "tlsf_free_post(\{params})"
  let bq = body_post(q)
  let large = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let bytes = "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd : \{ht})(m))))"
  let pre = "st(NIL,[\{i("m")},\{i("word(0)")},\{i("word(0)")}],(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{large},star(\{bytes},(fp : \{rty})(gs,ms)),h))"
  let popnative = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code((d : \{w})))"
  let pushnative = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let facts = "tlsf_physical_ok((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht})) && tlsf_bins_match(xs,hd,(bl : \{bt})) && MEM((m : \{w}),xs) && tlsf_used(hd(m))"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}"
  let focus = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let work = (l : String, r : String) => {
    "tlsf_free_work((d : \{w}),(lim : Num),(m : \{w}),\{focus},(hd : \{ht}),(fp : \{rty}),\{l},\{r})"
  }
  let start = inst(thm("tlsf_free_start"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    bq,
    "[\{bq}]",
    "(ys : \{lw})",
    "(zs : \{lw})",
    "(m : \{w})",
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(lim : Num)",
    "(top : \{w})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    i("word(0)"),
    i("word(0)"),
    "(fp : \{rty})",
  ])
  let _ = lemma(
    "tlsf_free_body_focused",
    "\{vars}, \{popnative} && \{pushnative} && \{facts} → sl_triple_g(G,fs,tabs,inst,\{bq},\{pre},tlsf_free_code(d,pop,push),\{bq},[\{bq}])",
    () => {
      seq([
        gen,
        strip,
        @tactics.undisch_tac(tm("MEM((m : \{w}),(xs : \{lw}))")),
        rw([@lists.mem_append_decompose()]),
        @tactics.disch_then(
          @tactics.x_choose_then(tm("(ys : \{lw})"))(
            @tactics.x_choose_then(tm("(zs : \{lw})"))(th => {
              @tactics.assume_tac(th)
            }),
          ),
        ),
        subst_vars(),
        rw([thm("tlsf_free_code_parts")]),
        @tactics.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(tm(work("F", "F"))),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_apply(start),
            seq([
              @tactics.match_mp_tac(thm("sl_seq_g")),
              @tactics.exists_tac(tm(work("T", "F"))),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.match_mp_tac(thm("tlsf_free_prev_phase")),
                    arw([]),
                  ]),
                  seq([
                    @tactics.match_mp_tac(thm("sl_seq_g")),
                    @tactics.exists_tac(tm(work("T", "T"))),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([
                          @tactics.match_mp_tac(thm("tlsf_free_next_phase")),
                          arw([]),
                        ]),
                        seq([
                          @tactics.match_mp_tac(thm("tlsf_free_finish")),
                          arw([]),
                        ]),
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
