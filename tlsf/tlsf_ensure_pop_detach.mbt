///|
fn prove_tlsf_ensure_pop_detach() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{v} : \{w})))"
  }
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      s = "star(\{ps[k]}, \{s})"
    }
    s
  }
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("m")}, \{i("n")}]"
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let oldxs = "APPEND((ys : \{lw}), CONS(\{m}, (zs : \{lw})))"
  let after = "APPEND((us : \{lw}), (vs : \{lw}))"
  let nfl = "tlsf_pop_fl(\{h}, (fl : \{w}), (sb : (Num) -> \{w}), \{after})"
  let nsb = "tlsf_pop_sb(\{h}, (sb : (Num) -> \{w}), \{after})"
  let nbl = "tlsf_pop_bl(\{h}, (bl : \{bt}), \{after})"
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, \{hd}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let detached = "tlsf_detached((d : \{w}), (lim : Num), (top : \{w}), (ys : \{lw}), \{m}, (zs : \{lw}), \{hd}, \{nfl}, \{nsb}, \{nbl})"
  let oldr = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (extent : Num) && star(\{large}, (fp : \{rty})(gs, ms), h)"
  let newr = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (extent : Num) && star(\{detached}, (fp : \{rty})(gs, ms), h)"
  let frameps = [
    cell("word_add(tlsf_base((d : " + w + ")), word(1908))", "top"),
    "tlsf_regions((word(0) : \{w}), (ys : \{lw}), \{hd})",
    cell(
      "word_add(\{m}, word(4))",
      "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
    ),
    "tlsf_spare(\{m}, \{h})",
    "tlsf_regions(\{m}, (zs : \{lw}), \{hd})",
  ]
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (extent : Num) && \{star(frameps)}(h)"
  let raw = inst(thm("tlsf_ensure_pop_invoke"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(pop : Num)",
    m,
    "(n : \{w})",
    h,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(us : \{lw})",
    "(vs : \{lw})",
    frame,
  ])
  let terms = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple_m", 7).unwrap()
  let field = (k : Int32) => {
    "val(word_add(\{m}, word(\{k}))) == val(\{m}) + \{k}"
  }
  let view = @basics.dest_imp(
      @kernel.concl(
        inst(thm("tlsf_payload_links"), [
          "val(\{m}) + 8",
          "val(tlsf_size(\{h}))",
        ]),
      ),
    ).1
  let rws = [
    thm("tlsf_detached"),
    thm("tlsf_large"),
    thm("tlsf_chain"),
    thm("tlsf_regions_append"),
    thm("tlsf_regions"),
    thm("tlsf_spare"),
    @kernel.assume_rule(tm(field(8))),
    @kernel.assume_rule(tm(field(12))),
    @kernel.assume_rule(view),
    arith("(a : Num) + 8 + 4 == a + 12 && a + 8 + 8 == a + 16"),
  ]
  let addr = "sfunc_ind((inst : Inst), (pop : Num))"
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf([T_num(T_i32)], NIL), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_pop_code((d : \{w})))"
  let cond = "\{native} && tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, \{hd}) && tlsf_bins_match(\{oldxs}, \{hd}, (bl : \{bt})) && !tlsf_used(\{h}) && (bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h})) == APPEND((us : \{lw}), CONS(\{m}, (vs : \{lw})))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ lim : Num, ∀ extent : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_ensure_pop_detach",
    "\{vars}, \{cond} → sl_triple_m(fs, tabs, inst, st(NIL, \{lc}, \{oldr}), [Local_get(0), Call(pop)], st(NIL, \{lc}, \{newr}), NIL)",
    () => {
      seq([
        gen,
        strip,
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
        have(
          "16 <= val(tlsf_size(\{h}))",
          seq([
            @tactics.undisch_tac(
              tm("tlsf_block_ok(val(\{m}), (lim : Num), \{m}, \{hd})"),
            ),
            rw([thm("tlsf_block_ok")]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        seq(
          [8, 12].map(k => {
            have(
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
        have(
          show(view),
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_payload_links"), [
                "val(\{m}) + 8",
                "val(tlsf_size(\{h}))",
              ]),
            ),
            @int.asm_arith_tac,
          ]),
        ),
        have(
          "tlsf_bins_match(\{oldxs}, tlsf_mark(\{hd}, \{m}), \{nbl})",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_pop_bins_match"), [
                oldxs,
                hd,
                "(bl : \{bt})",
                m,
                "(us : \{lw})",
                "(vs : \{lw})",
              ]),
            ),
            arw([@lists.mem_append(), @lists.mem()]),
          ]),
        ),
        @tactics.match_mp_tac(thm("sl_conseq_m")),
        @tactics.exists_tac(terms[3]),
        @tactics.exists_tac(terms[5]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            ent_tac(rws, []),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([@tactics.match_mp_tac(raw), arw([])]),
                ent_tac(rws, [
                  "tlsf_prev((us : \{lw}))",
                  "tlsf_hd((vs : \{lw}))",
                ]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
