///|
fn prove_tlsf_free_pop_pair() -> Unit raise {
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
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    out
  }
  let hd = "(hd : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},(zs : \{lw}))))"
  let removed = "APPEND((us : \{lw}),(vs : \{lw}))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ lc0 : List[Value], ∀ fp : \{rty}"
  let native = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code((d : \{w})))"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let other = if prev { m } else { r }
    let h = "\{hd}(\{other})"
    let ys0 = if prev { "APPEND((ys : \{lw}),[\{m}])" } else { "(ys : \{lw})" }
    let zs0 = if prev { "(zs : \{lw})" } else { "CONS(\{r},(zs : \{lw}))" }
    let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),\{ys0},\{active},\{zs0},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
    let nfl = "tlsf_pop_fl(\{h},(fl : \{w}),(sb : (Num) -> \{w}),\{removed})"
    let nsb = "tlsf_pop_sb(\{h},(sb : (Num) -> \{w}),\{removed})"
    let nbl = "tlsf_pop_bl(\{h},(bl : \{bt}),\{removed})"
    let pair = "tlsf_free_pair((d : \{w}),(top : \{w}),(ys : \{lw}),\{m},\{r},(zs : \{lw}),\{hd},\{nfl},\{nsb},\{nbl})"
    let p = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pending},(fp : \{rty})(gs,ms),h)"
    let q = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pair},(fp : \{rty})(gs,ms),h)"
    let ps = [
      cell("tlsf_top_cell((d : " + w + "))", "top"),
      "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
      cell(
        "word_add(\{m},word(4))",
        "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
      ),
      cell("word_add(\{r},word(4))", "m"),
      "tlsf_regions(\{r},(zs : \{lw}),\{hd})",
      cell(active, "\{hd}(\{active})"),
      "tlsf_bytes(val(\{active})+8,val(tlsf_size(\{hd}(\{active}))))",
      "tlsf_spare(\{other},\{h})",
    ]
    let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(ps)}(h)"
    let raw = @simp.rewrite_rule(ths([@class.eta_ax()]))(
      inst(thm("tlsf_free_pop_invoke"), [
        "(fs : List[Cl])",
        "(tabs : List[(Tab_t,List[V_ref])])",
        "(inst : Inst)",
        "(d : \{w})",
        "(pop : Num)",
        other,
        "(lc0 : List[Value])",
        h,
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "(us : \{lw})",
        "(vs : \{lw})",
        frame,
      ]),
    )
    let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple_m", 7).unwrap()
    let cond = "\{native} && tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active}) && !tlsf_used(\{hd}(\{m})) && !tlsf_used(\{hd}(\{r})) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{active}),(bl : \{bt})) && (bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h})) == APPEND((us : \{lw}),CONS(\{other},(vs : \{lw})))"
    let field = (k : Int32) => {
      "val(word_add(\{other},word(\{k}))) == val(\{other})+\{k}"
    }
    let view = @basics.dest_imp(
        @kernel.concl(
          inst(thm("tlsf_payload_links"), [
            "val(\{other})+8",
            "val(tlsf_size(\{h}))",
          ]),
        ),
      ).1
    let rws = [
      thm("tlsf_free_pending"),
      thm("tlsf_free_pair"),
      thm("tlsf_regions_append"),
      thm("tlsf_regions"),
      thm("tlsf_spare"),
      thm("tlsf_free_end_append"),
      thm("tlsf_end"),
      thm("tlsf_top_cell"),
      @kernel.assume_rule(tm(field(8))),
      @kernel.assume_rule(tm(field(12))),
      @kernel.assume_rule(view),
      arith("(a : Num)+8+4 == a+12 && a+8+8 == a+16"),
    ]
    let _ = lemma(
      if prev {
        "tlsf_free_pop_prev_pair"
      } else {
        "tlsf_free_pop_next_pair"
      },
      "\{vars}, \{cond} → sl_triple_m(fs,tabs,inst,st([\{i(other)}],(lc0 : List[Value]),\{p}),[Call(pop)],st(NIL,lc0,\{q}),NIL)",
      () => {
        seq([
          gen,
          strip,
          @tactics.mp_tac(
            inst(thm("tlsf_free_pair_facts"), [
              "(ys : \{lw})",
              "(zs : \{lw})",
              m,
              r,
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(lim : Num)",
              "(top : \{w})",
              hd,
            ]),
          ),
          @tactics.undisch_tac(
            tm(
              "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active})",
            ),
          ),
          rw([thm("tlsf_free_geom_facts")]),
          strip,
          arw([]),
          strip,
          free_have(
            "16 <= val(tlsf_size(\{h}))",
            seq([
              @tactics.undisch_tac(
                tm("tlsf_block_ok(val(\{other}),(lim : Num),\{other},\{hd})"),
              ),
              rw([thm("tlsf_block_ok")]),
              @meson.meson_tac(ths([])),
            ]),
          ),
          seq(
            [8, 12].map(k => {
              free_have(
                field(k),
                seq([
                  @tactics.match_mp_tac(
                    inst(thm("tlsf_block_field_address"), [
                      "val(\{other})",
                      "(lim : Num)",
                      other,
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
          free_have(
            show(view),
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_payload_links"), [
                  "val(\{other})+8",
                  "val(tlsf_size(\{h}))",
                ]),
              ),
              @int.asm_arith_tac,
            ]),
          ),
          @tactics.match_mp_tac(thm("sl_conseq_m")),
          @tactics.exists_tac(rt[3]),
          @tactics.exists_tac(rt[5]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              ent_tac(rws, []),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([@tactics.match_mp_tac(raw), arw([])]),
                  ent_tac(rws, [
                    "tlsf_prev((us : " + lw + "))",
                    "tlsf_hd((vs : " + lw + "))",
                  ]),
                ]),
              ),
            ]),
          ),
        ])
      },
    )
  }
}
