///|
fn prove_tlsf_free_publish() -> Unit raise {
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
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},(zs : \{lw})))"
  let nfl = "tlsf_push_fl(\{h},(fl : \{w}))"
  let nsb = "tlsf_push_sb(\{h},(sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{h},\{m},(bl : \{bt}))"
  let ready = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{m}) && !tlsf_used(\{h}) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{m}),(bl : \{bt})) && tlsf_free_left((ys : \{lw}),hd) && tlsf_free_right((zs : \{lw}),hd)"
  let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),\{m},(zs : \{lw}),\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let large = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{nfl},\{nsb},\{nbl})"
  let rp = (p : String) => {
    "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{p},(fp : \{rty})(gs,ms),h)"
  }
  let ps = [
    cell("tlsf_top_cell((d : " + w + "))", "top"),
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
    cell(
      "word_add(\{m},word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    "tlsf_spare(\{m},\{h})",
    "tlsf_regions(\{m},(zs : \{lw}),\{hd})",
  ]
  let mut framed = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  for k = ps.length() - 1; k >= 0; k = k - 1 {
    framed = "star(\{ps[k]},\{framed})"
  }
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{framed}(h)"
  let raw = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(thm("tlsf_free_push_invoke"), [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      "(d : \{w})",
      "(push : Num)",
      m,
      "(lc0 : List[Value])",
      h,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(pf0 : \{w})",
      "(nf0 : \{w})",
      frame,
    ]),
  )
  let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple_m", 7).unwrap()
  let ex = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ pf0 : \{w}, ∃ nf0 : \{w}, (\{show(rt[3])})(vs,lc,gs,ms,h)"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ lc0 : List[Value], ∀ fp : \{rty}"
  let field = (k : Int32) => "val(word_add(\{m},word(\{k}))) == val(\{m})+\{k}"
  let view = @basics.dest_imp(
      @kernel.concl(
        inst(thm("tlsf_payload_links"), ["val(\{m})+8", "val(tlsf_size(\{h}))"]),
      ),
    ).1
  let before = [
    thm("tlsf_free_pending"),
    thm("tlsf_spare"),
    thm("tlsf_top_cell"),
    @kernel.assume_rule(tm(field(8))),
    @kernel.assume_rule(tm(field(12))),
    @kernel.assume_rule(view),
    arith("(a : Num)+8+4 == a+12 && a+8+8 == a+16"),
  ]
  let after = [
    thm("tlsf_large"),
    thm("tlsf_chain"),
    thm("tlsf_regions_append"),
    thm("tlsf_regions"),
    thm("tlsf_top_cell"),
  ]
  let _ = lemma(
    "tlsf_free_publish_call",
    "\{vars}, \{native} && (\{ready}) → sl_triple_m(fs,tabs,inst,st([\{i("m")}],(lc0 : List[Value]),\{rp(pending)}),[Call(push)],st([\{i("word(0)")}],lc0,\{rp(large)}),NIL)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_free_ready_physical"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          m,
          "(d : \{w})",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_block"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          m,
          "(d : \{w})",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([]),
      strip,
      free_have(
        "!(\{m} == word(0)) && 16 <= val(tlsf_size(\{h}))",
        seq([
          @tactics.undisch_tac(
            tm("tlsf_block_ok(val(\{m}),(lim : Num),\{m},\{hd})"),
          ),
          rw([thm("tlsf_block_ok")]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      split_conjs(),
      free_have(
        "tlsf_bins_match(\{xs},\{hd},\{nbl})",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_extend_bins"), [xs, hd, hd, "(bl : \{bt})", m]),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
        ]),
      ),
      seq(
        [8, 12].map(k => {
          free_have(
            field(k),
            seq([
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
      free_have(
        show(view),
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_payload_links"), [
              "val(\{m})+8",
              "val(tlsf_size(\{h}))",
            ]),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      free_at("publish consequence", @tactics.match_mp_tac(thm("sl_conseq_m"))),
      @tactics.exists_tac(tm(ex)),
      @tactics.exists_tac(rt[5]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          ent_tac(before, ["(pf : \{w})", "(nf : \{w})"]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              seq([
                free_at(
                  "publish existential",
                  @tactics.match_mp_tac(thm("sl_ex_m")),
                ),
                beta_goal(),
                @tactics.x_gen_tac(tm("(pf0 : \{w})")),
                free_at(
                  "publish existential",
                  @tactics.match_mp_tac(thm("sl_ex_m")),
                ),
                beta_goal(),
                @tactics.x_gen_tac(tm("(nf0 : \{w})")),
                rw([@class.eta_ax()]),
                free_at("publish native call", @tactics.match_mp_tac(raw)),
                arw([]),
              ]),
              ent_tac(after, []),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
