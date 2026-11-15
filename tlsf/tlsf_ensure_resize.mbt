///|
fn prove_tlsf_ensure_resize() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let star = (ps : Array[String]) => {
    let mut o = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      o = "star(\{ps[k]},\{o})"
    }
    o
  }
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let cap = "tlsf_capacity_at((lim2 : Num),\{m})"
  let nh = "tlsf_extend_headers(\{hd},\{m},(lim2 : Num))"
  let rh = "word_or(\{cap},word_and(\{h},word(3)))"
  let nfl = "tlsf_push_fl(\{rh},(fl : \{w}))"
  let nsb = "tlsf_push_sb(\{rh},(sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{rh},\{m},(bl : \{bt}))"
  let prefix = "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})"
  let prev = "tlsf_end((word(0) : \{w}),(ys : \{lw}))"
  let metadata = [
    cell("tlsf_top_cell((d : " + w + "))", "m"),
    prefix,
    cell("word_add(\{m},word(4))", prev),
  ]
  let payload = "tlsf_bytes(val(\{m})+8,val(\{cap}))"
  let bins = "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let preR = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && \{star(metadata+[cell("m",h),payload,bins])}(h)"
  let large = "tlsf_large((d : \{w}),(lim2 : Num),\{m},\{xs},\{nh},\{nfl},\{nsb},\{nbl})"
  let postR = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && star(\{large},(fp : \{rty})(gs,ms),h)"
  let lc = "[\{i("m")},\{i("e")}]"
  let frame = "(gs : List[Value]) => (ms : Num) => \{star(metadata+["tlsf_bytes(val(\{m})+16,val(\{cap})-8)"])}"
  let raw = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("tlsf_ensure_free_tail_raw"), [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      "(d : \{w})",
      "(pop : Num)",
      "(push : Num)",
      m,
      h,
      "(e : \{w})",
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(pf0 : \{w})",
      "(nf0 : \{w})",
      frame,
      "(lim2 : Num)",
    ]),
  )
  let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple_m", 7).unwrap()
  let existsP = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ pf0 : \{w}, ∃ nf0 : \{w}, (\{show(rt[3])})(vs,lc,gs,ms,h)"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd})"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let cond = "\{native} && \{old} && !tlsf_used(\{h}) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{m}),(bl : \{bt})) && (lim : Num) <= (lim2 : Num) && lim2 <= 4294967296 && MOD(lim2,65536) == 0"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ e : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}, ∀ lim : Num, ∀ lim2 : Num"
  let agree = "∀ x : \{w}, MEM(x,(ys : \{lw})) → \{hd}(x) == (\{nh})(x)"
  let close = inst(thm("tlsf_ensure_extend_close"), [
    "(ys : \{lw})",
    "(d : \{w})",
    "(lim2 : Num)",
    m,
    hd,
    nh,
    nfl,
    nsb,
    nbl,
    "(fp : \{rty})((gs : List[Value]),(ms : Num))",
  ])
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let post = seq([
    gen,
    rw([thm("st")] + lift_rws()),
    strip,
    @tactics.mp_tac(close),
    arw([]),
    @tactics.disch_then(th => @tactics.subst1_tac(@equal.sym(th))),
    arw([]),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw([thm("tlsf_spare"), thm("tlsf_top_cell")] + lift_rws() + ac),
  ])
  let _ = lemma(
    "tlsf_ensure_resize",
    "\{vars}, \{cond} → sl_triple_m(fs,tabs,inst,st(NIL,\{lc},\{preR}),\{show(rt[4])},st(NIL,\{lc},\{postR}),NIL)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_extend_model"), [
          "(ys : \{lw})",
          "(d : \{w})",
          "(lim : Num)",
          "(lim2 : Num)",
          m,
          hd,
        ]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_ensure_top_facts"), [
          "(ys : \{lw})",
          "(d : \{w})",
          "(lim2 : Num)",
          m,
          nh,
        ]),
      ),
      arw([]),
      strip,
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([@kernel.assume_rule(tm("(\{nh})(\{m}) == \{rh}"))]),
        ),
      ),
      have(
        "(\{nh})(\{m}) == \{rh}",
        rw([thm("tlsf_extend_headers"), thm("tlsf_put")]),
      ),
      have(
        "tlsf_bins_match(\{xs},\{nh},\{nbl})",
        seq([
          @tactics.match_mp_tac(
            @simp.rewrite_rule(
              ths([@kernel.assume_rule(tm("(\{nh})(\{m}) == \{rh}"))]),
            )(inst(thm("tlsf_extend_bins"), [xs, hd, nh, "(bl : \{bt})", m])),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
          gen,
          @tactics.disch_tac,
          rw([thm("tlsf_extend_headers"), thm("tlsf_put")]),
          arw([]),
        ]),
      ),
      seq(
        [8, 12].map(k => {
          have(
            "val(word_add(\{m},word(\{k}))) == val(\{m})+\{k}",
            seq([
              @tactics.mp_tac(
                inst(thm("tlsf_focus_block"), [
                  "(ys : \{lw})",
                  "(NIL : \{lw})",
                  m,
                  "(d : \{w})",
                  "(lim : Num)",
                  m,
                  hd,
                ]),
              ),
              arw([]),
              strip,
              @tactics.match_mp_tac(
                inst(thm("tlsf_block_field_address"), [
                  "val(\{m})",
                  "(lim : Num)",
                  m,
                  hd,
                  k.to_string(),
                ]),
              ),
              arw([]),
              @tactics.conv_tac(@calc_num.num_reduce_conv),
            ]),
          )
        }),
      ),
      have("8 <= val(\{cap})", @int.asm_arith_tac),
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(tm(existsP)),
      @tactics.exists_tac(tm("st(NIL,\{lc},\{postR})")),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              ent_tac(
                [
                  @bool.undisch(
                    inst(thm("tlsf_payload_links"), [
                      "val(\{m})+8",
                      "val(\{cap})",
                    ]),
                  ),
                  arith("(a : Num)+8+4 == a+12 && a+8+8 == a+16"),
                  thm("tlsf_top_cell"),
                ],
                ["(pf : \{w})", "(nf : \{w})"],
              ),
            ]),
          ),
          solve(
            seq([
              @tactics.match_mp_tac(thm("sl_ex_m")),
              beta_goal(),
              @tactics.x_gen_tac(tm("(pf0 : \{w})")),
              @tactics.match_mp_tac(thm("sl_ex_m")),
              beta_goal(),
              @tactics.x_gen_tac(tm("(nf0 : \{w})")),
              @tactics.match_mp_tac(thm("sl_conseq_m")),
              @tactics.exists_tac(rt[3]),
              @tactics.exists_tac(rt[5]),
              rw([]),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      @tactics.match_mp_tac(raw),
                      arw([@equal.gsym(@words.val_eq_0())]),
                      @int.asm_arith_tac,
                    ]),
                  ),
                  solve(seq([gen, beta_goal(), strip, arw([])])),
                  solve(post),
                ]),
              ),
            ]),
          ),
          solve(seq([gen, beta_goal(), strip, arw([])])),
        ]),
      ),
    ]),
  )
}
