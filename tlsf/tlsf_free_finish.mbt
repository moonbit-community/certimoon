///|
fn prove_tlsf_free_finish() -> Unit raise {
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
  let same = seq([gen, beta_goal(), strip, arw([])])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let params = "(d : \{w}),(m0 : \{w}),(lim : Num),(top0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fl0 : \{w}),(sb0 : (Num) -> \{w}),(bl0 : \{bt}),(fp : \{rty})"
  let q = "tlsf_free_post(\{params})"
  let bq = body_post(q)
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ d : \{w}, ∀ pop : Num, ∀ push : Num"
  let original = "∀ m0 : \{w}, ∀ lim : Num, ∀ top0 : \{w}, ∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ fl0 : \{w}, ∀ sb0 : (Num) -> \{w}, ∀ bl0 : \{bt}, ∀ fp : \{rty}"
  let current = "∀ top : \{w}, ∀ ys : \{lw}, ∀ m : \{w}, ∀ zs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value"
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let lc = "[\{i("m")},(l1 : Value),(l2 : Value)]"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let cond = "\{native} && tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht}),(m : \{w})) && !tlsf_used(hd(m)) && tlsf_bins_match(\{xs},tlsf_mark(hd,m),(bl : \{bt})) && tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),m,hd) && tlsf_free_live((xs0 : \{lw}),hd0,m0,\{xs},hd) && tlsf_free_left((ys : \{lw}),hd) && tlsf_free_right((zs : \{lw}),hd)"
  let pushth = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("tlsf_free_publish_call"), [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      "(d : \{w})",
      "(push : Num)",
      "(ys : \{lw})",
      "(zs : \{lw})",
      "(m : \{w})",
      "(lim : Num)",
      "(top : \{w})",
      "(hd : \{ht})",
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      lc,
      "(fp : \{rty})",
    ]),
  )
  let pt = args_of(@basics.dest_imp(@kernel.concl(pushth)).1, "sl_triple_m", 7).unwrap()
  let stp = args_of(pt[3], "st", 3).unwrap()
  let rr = show(stp[2])
  let get = sym_prove(
    "tlsf_free_publish_arg",
    "∀ m : \{w}, ∀ l1 : Value, ∀ l2 : Value, ∀ R : \{rty}, sl_triple(st(NIL,\{lc},R),[Local_get(0)],st([\{i("m")}],\{lc},R))",
    [],
    () => [],
    kind="lemma",
  )
  let get = inst(get, ["(m : \{w})", "(l1 : Value)", "(l2 : Value)", rr])
  let h = "(hd : \{ht})((m : \{w}))"
  let nfl = "tlsf_push_fl(\{h},(fl : \{w}))"
  let nsb = "tlsf_push_sb(\{h},(sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{h},(m : \{w}),(bl : \{bt}))"
  let _ = lemma(
    "tlsf_free_finish_focused",
    "\{env}, \{original}, \{current}, \{cond} → sl_triple_g(G,fs,tabs,inst,rp,st(NIL,\{lc},\{rr}),tlsf_free_publish(d,pop,push),\{bq},labels)",
    () => {
      seq([
        gen,
        strip,
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(
            ths([thm("tlsf_free_covers"), thm("tlsf_free_live")]),
          ),
        ),
        split_conjs(),
        rw([thm("tlsf_free_publish")]),
        @tactics.match_mp_tac(thm("sl_cons_g")),
        @tactics.exists_tac(pt[3]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_at("finish arg", free_lift(get)),
            free_at(
              "finish call",
              free_g_conseq(
                pushth,
                same,
                ent_tac(
                  [
                    thm("tlsf_free_post"),
                    thm("tlsf_free_covers"),
                    thm("tlsf_free_live"),
                    @lists.mem_append(),
                    @lists.mem(),
                  ],
                  [
                    "(top : \{w})",
                    xs,
                    "(hd : \{ht})",
                    nfl,
                    nsb,
                    nbl,
                    "(m : \{w})",
                  ],
                ),
              ),
            ),
          ]),
        ),
      ])
    },
  )
  let work = "tlsf_free_work((d : \{w}),(lim : Num),(m0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fp : \{rty}),T,T)"
  let _ = lemma(
    "tlsf_free_finish",
    "\{env}, \{original}, \{native} → sl_triple_g(G,fs,tabs,inst,rp,\{work},tlsf_free_publish(d,pop,push),\{bq},labels)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.conv_tac(
          pre_conv(@simp.rewrite_conv(ths([thm("tlsf_free_work")]))),
        ),
        free_intro(),
        free_at("finish work", free_apply(thm("tlsf_free_finish_focused"))),
      ])
    },
  )
}
