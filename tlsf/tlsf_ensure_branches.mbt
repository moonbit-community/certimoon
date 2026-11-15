// Both complete growth branches, with the public ensure postcondition.

///|
fn prove_tlsf_ensure_branches() -> Unit raise {
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
  let d = "(d : \{w})"
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let s = "(s : \{w})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let e = "tlsf_ensure_expected(\{s})"
  let lc = "[\{i(m)},\{i(e)}]"
  let model = [
    d,
    "(lim : Num)",
    "(ys : \{lw})",
    m,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
  ]
  let saved = "tlsf_ensure_saved(\{model.join(",")},(before : \{heap}))"
  let params = [
    d,
    s,
    "(lim : Num)",
    m,
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
  let ready = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && \{q}([\{i("word(1)")}],gs,ms,h)"
  let old = "tlsf_physical_ok(\{d},(lim : Num),\{m},\{xs},\{hd})"
  let facts = "\{old} && tlsf_bins_match(\{xs},\{hd},(bl : \{bt})) && 16 <= val(\{s}) && val(s) <= 4160749568"
  let popnative = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code(\{d}))"
  let pushnative = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(\{d}))"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ s : \{w}, ∀ lim : Num, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ labels : List[\{sassn}]"
  let env = [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    rp,
  ]
  let frozen = "(gs : List[Value]) => (ms : Num) => (fp : \{rty})(gs,(lim : Num))"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  for used in [false, true] {
    let part = if used { "used" } else { "free" }
    let amount = if used {
      "word_jushr(word_add(\{e},word(65543)),word(16))"
    } else {
      "word_jushr(word_add(word_sub(\{e},tlsf_size(\{h})),word(65535)),word(16))"
    }
    let delta = "val(\{amount})*65536"
    let lim2 = "(lim : Num)+\{delta}"
    let r = if used { "(word((lim : Num)) : \{w})" } else { m }
    let after = "APPEND((us : \{lw}),(bs : \{lw}))"
    let bfl = if used {
      "(fl : \{w})"
    } else {
      "tlsf_pop_fl(\{h},(fl : \{w}),(sb : (Num) -> \{w}),\{after})"
    }
    let bsb = if used {
      "(sb : (Num) -> \{w})"
    } else {
      "tlsf_pop_sb(\{h},(sb : (Num) -> \{w}),\{after})"
    }
    let bbl = if used {
      "(bl : \{bt})"
    } else {
      "tlsf_pop_bl(\{h},(bl : \{bt}),\{after})"
    }
    let rh = if used {
      "word_or(tlsf_capacity_at(\{lim2},\{r}),word(2))"
    } else {
      "word_or(tlsf_capacity_at(\{lim2},\{r}),word_and(\{h},word(3)))"
    }
    let nfl = "tlsf_push_fl(\{rh},\{bfl})"
    let nsb = "tlsf_push_sb(\{rh},\{bsb})"
    let nbl = "tlsf_push_bl(\{rh},\{r},\{bbl})"
    let helperargs = [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      d,
      "(pop : Num)",
      "(push : Num)",
      "(ys : \{lw})",
      m,
      e,
      hd,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
    ]
    let helper = inst(
      thm("tlsf_ensure_" + part + "_success"),
      helperargs +
      (if used { [] } else { ["(us : \{lw})", "(bs : \{lw})"] }) +
      [frozen, "(lim : Num)", delta],
    )
    let helper = @simp.rewrite_rule(ths([@class.eta_ax()]))(helper)
    let mt = args_of(
      @basics.dest_imp(@kernel.concl(helper)).1,
      "sl_triple_m",
      7,
    ).unwrap()
    let control = inst(
      thm("tlsf_ensure_grow_control"),
      env +
      [
        d,
        "(pop : Num)",
        "(push : Num)",
        lc,
        "(lim : Num)",
        amount,
        saved,
        show(mt[4]),
        ready,
        "(labels : List[\{sassn}])",
      ],
    )
    let ct = args_of(
      @basics.dest_imp(@kernel.concl(control)).1,
      "sl_triple_g",
      9,
    ).unwrap()
    let amount_th = if used {
      inst(thm("tlsf_ensure_used_amount_raw"), [
        d, "(pop : Num)", "(push : Num)", m, e, saved,
      ])
    } else {
      inst(
        thm("tlsf_ensure_free_amount_saved"),
        model + ["(before : \{heap})", e, "(pop : Num)", "(push : Num)"],
      )
    }
    let amount_th = @simp.rewrite_rule(ths([@class.eta_ax()]))(amount_th)
    let amt_body = if @basics.is_imp(@kernel.concl(amount_th)) {
      @basics.dest_imp(@kernel.concl(amount_th)).1
    } else {
      @kernel.concl(amount_th)
    }
    let at = args_of(amt_body, "sl_triple", 3).unwrap()
    let body = "tlsf_ensure_" + part + "_body(\{d},(pop : Num),(push : Num))"
    let body_eq = @tactics.prove(
      tm("\{body} == APPEND(\{show(at[1])},\{show(ct[6])})"),
      rw([thm("tlsf_ensure_" + part + "_body"), @lists.append()]),
    )
    let post_th = inst(thm("tlsf_ensure_success_post"), [
      d,
      s,
      "(lim : Num)",
      "(ys : \{lw})",
      m,
      hd,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(before : \{heap})",
      "(fp : \{rty})",
      nfl,
      nsb,
      nbl,
      "(gs : List[Value])",
      "(ms : Num)",
      "(h : \{heap})",
    ])
    let post = seq([
      gen,
      rw([thm("st")] + lift_rws()),
      strip,
      arw([]),
      @tactics.match_mp_tac(post_th),
      arw(
        [
          thm("tlsf_ensure_pages"),
          thm("tlsf_grow_top"),
          thm("tlsf_grow_chain"),
          thm("tlsf_grow_headers"),
          @equal.gsym(@lists.append_assoc()),
          @lists.append(),
        ] +
        ac,
      ),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(ac),
    ])
    let pre = seq([
      gen,
      rw([thm("st")] + lift_rws()),
      strip,
      arw([]),
      @tactics.mp_tac(
        inst(
          thm("tlsf_ensure_saved_growth_frame"),
          model +
          ["(before : \{heap})", delta, "(gs : List[Value])", "(h : \{heap})"],
        ),
      ),
      arw(ac),
    ])
    let success = seq([
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_grow_limits"), ["(lim : Num)", amount])),
      arw([]),
      strip,
      if used {
        seq([
          have(
            "16 <= val(\{e}) && val(\{e}) <= 4160749568",
            seq([
              @tactics.mp_tac(inst(thm("tlsf_ensure_expected_bounds"), [s])),
              arw([]),
              @meson.meson_tac(ths([])),
            ]),
          ),
          @tactics.mp_tac(inst(thm("tlsf_used_pages_fit"), [e])),
          arw([]),
          strip,
          have("24 <= \{delta}", @int.asm_arith_tac),
        ])
      } else {
        @tactics.all_tac
      },
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(mt[3]),
      @tactics.exists_tac(mt[5]),
      @tactics.exists_tac(tm("(labels : List[\{sassn}])")),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.match_mp_tac(thm("sl_triple_g_of_m_closed")),
              @tactics.match_mp_tac(helper),
              arw([]),
              @int.asm_arith_tac,
            ]),
          ),
          solve(pre),
          solve(post),
          solve(same),
        ]),
      ),
    ])
    let fail = seq([
      gen,
      beta_goal(),
      rw([thm("tlsf_ensure_saved"), thm("tlsf_ensure_post")]),
      strip,
      @tactics.try_tac(@tactics.disj1_tac),
      arw([]),
    ])
    let bincond = if used {
      ""
    } else {
      " && (bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h})) == APPEND((us : \{lw}),CONS(\{m},(bs : \{lw})))"
    }
    let uv = if used { "" } else { ", ∀ us : \{lw}, ∀ bs : \{lw}" }
    let flag = if used { "tlsf_used(\{h})" } else { "!tlsf_used(\{h})" }
    let _ = lemma(
      "tlsf_ensure_" + part + "_branch",
      "\{vars}\{uv}, \{facts} && \{popnative} && \{pushnative} && \{flag}\{bincond} → sl_triple_g(G,fs,tabs,inst,\{rp},st(NIL,\{lc},\{saved}),\{body},\{ready},labels)",
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_ensure_top_facts"), [
            "(ys : \{lw})",
            d,
            "(lim : Num)",
            m,
            hd,
          ]),
        ),
        arw([]),
        strip,
        rw([body_eq]),
        @tactics.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(ct[5]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.match_mp_tac(thm("sl_conseq_g")),
              @tactics.exists_tac(at[0]),
              @tactics.exists_tac(at[2]),
              @tactics.exists_tac(tm("(labels : List[\{sassn}])")),
              rw([]),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      @tactics.match_mp_tac(thm("sl_triple_g_of")),
                      @tactics.conj_tac,
                      @tactics.first(
                        @list.List([
                          solve(call_free_tac()),
                          solve(
                            seq([
                              @tactics.match_mp_tac(thm("sl_triple_l_of")),
                              if @basics.is_imp(@kernel.concl(amount_th)) {
                                seq([@tactics.match_mp_tac(amount_th), arw([])])
                              } else {
                                @tactics.accept_tac(amount_th)
                              },
                            ]),
                          ),
                        ]),
                      ),
                    ]),
                  ),
                  solve(same),
                  solve(
                    seq([
                      gen,
                      rw([thm("st"), thm("tlsf_ensure_saved")]),
                      strip,
                      arw([]),
                    ]),
                  ),
                ]),
              ),
            ]),
            seq([
              @tactics.match_mp_tac(control),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([solve(arw([])), solve(fail), solve(success)]),
              ),
            ]),
          ]),
        ),
      ]),
    )
  }
}
