///|
fn prove_tlsf_ensure_append() -> Unit raise {
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
  let r = "(word((lim : Num)) : \{w})"
  let rraw = "word_add(word_add(\{m},word(8)),tlsf_size(\{h}))"
  let cap = "tlsf_capacity_at((lim2 : Num),\{r})"
  let nh = "tlsf_append_headers(\{hd},\{m},(lim : Num),(lim2 : Num))"
  let rh = "word_or(\{cap},word(2))"
  let nfl = "tlsf_push_fl(\{rh},(fl : \{w}))"
  let nsb = "tlsf_push_sb(\{rh},(sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{rh},\{r},(bl : \{bt}))"
  let prefix = "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})"
  let prev = "tlsf_end((word(0) : \{w}),(ys : \{lw}))"
  let metadata = [prefix, cell("word_add(\{m},word(4))", prev)]
  let payload = "tlsf_bytes(val(\{r})+8,val(\{cap}))"
  let bins = "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let preR = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && \{star(metadata+[cell("tlsf_top_cell((d : " + w + "))","m"),cell("m",h),cell(r,"word(0)"),cell("word_add(\{r},word(4))","word(0)"),payload,bins])}(h)"
  let nx = "APPEND((ys : \{lw}),[\{m},\{r}])"
  let large = "tlsf_large((d : \{w}),(lim2 : Num),\{r},\{nx},\{nh},\{nfl},\{nsb},\{nbl})"
  let postR = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && star(\{large},(fp : \{rty})(gs,ms),h)"
  let lc0 = "[\{i("m")},\{i("e")}]"
  let lc1 = "[\{i("m")},\{i(r)}]"
  let frame = "(gs : List[Value]) => (ms : Num) => \{star(metadata+["tlsf_bytes(val(\{r})+16,val(\{cap})-8)"])}"
  let raw0 = inst(thm("tlsf_ensure_used_tail_raw"), [
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
  ])
  let raw = @simp.rewrite_rule(
    ths([@class.eta_ax(), @kernel.assume_rule(tm("\{rraw} == \{r}"))]),
  )(raw0)
  let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple_m", 7).unwrap()
  let existsP = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ pf0 : \{w}, ∃ nf0 : \{w}, (\{show(rt[3])})(vs,lc,gs,ms,h)"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd})"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let cond = "\{native} && \{old} && tlsf_used(\{h}) && tlsf_bins_match(\{xs},\{hd},(bl : \{bt})) && (lim : Num)+24 <= (lim2 : Num) && lim2 <= 4294967296 && MOD(lim2,65536) == 0"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ e : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}, ∀ lim : Num, ∀ lim2 : Num"
  let close = inst(thm("tlsf_ensure_append_close"), [
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
    r,
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
    "tlsf_ensure_append",
    "\{vars}, \{cond} → sl_triple_m(fs,tabs,inst,st(NIL,\{lc0},\{preR}),\{show(rt[4])},st(NIL,\{lc1},\{postR}),NIL)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_append_model"), [
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
          "(lim : Num)",
          m,
          hd,
        ]),
      ),
      arw([]),
      strip,
      have("val(\{m})+8 < 4294967296", @int.asm_arith_tac),
      have(
        "val(word_add(\{m},word(8))) == val(\{m})+8",
        seq([@tactics.match_mp_tac(thm("val_add_small")), arw([])]),
      ),
      have(
        "val(\{rraw}) == (lim : Num)",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_val_add_exact"), [
              "word_add(\{m},word(8))",
              "tlsf_size(\{h})",
            ]),
          ),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      have(
        "\{rraw} == \{r}",
        seq([rw([@equal.gsym(@words.val_eq())]), arw([])]),
      ),
      have(
        "MOD((lim2 : Num),8) == 0 && MOD((lim : Num),8) == 0",
        seq([
          @tactics.conj_tac,
          @tactics.match_mp_tac(thm("tlsf_page_aligned8")),
          arw([]),
        ]),
      ),
      have("0 < (lim : Num)", @int.asm_arith_tac),
      @tactics.mp_tac(inst(thm("tlsf_capacity_fields"), ["(lim2 : Num)", r])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_new_top_fields"), [cap])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_clear_last_fields"), [h])),
      strip,
      have(
        "tlsf_used((\{nh})(\{m}))",
        seq([
          rw([thm("tlsf_append_headers"), thm("tlsf_put")]),
          arw([]),
          @meson.asm_meson_tac(ths([])),
        ]),
      ),
      have(
        "tlsf_bins_match(\{nx},\{nh},\{nbl})",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_append_bins"), [xs, hd, "(bl : \{bt})", m, r, rh]),
          ),
          arw([
            thm("tlsf_append_headers"),
            @equal.gsym(@lists.append_assoc()),
            @lists.append(),
          ]),
        ]),
      ),
      seq(
        [4, 8, 12].map(k => {
          have(
            "val(word_add(\{r},word(\{k}))) == val(\{r})+\{k}",
            seq([
              @tactics.match_mp_tac(thm("val_add_small")),
              @int.asm_arith_tac,
            ]),
          )
        }),
      ),
      have("8 <= val(\{cap})", @int.asm_arith_tac),
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(tm(existsP)),
      @tactics.exists_tac(tm("st(NIL,\{lc1},\{postR})")),
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
                      "(lim : Num)+8",
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
