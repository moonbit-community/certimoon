// Lift the word-level store triples to the startup ownership predicate.

///|
fn prove_tlsf_initialize_stores() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let m = "tlsf_initialize_origin(\{d})"
  let hdr = "tlsf_initialize_header(\{d},\{lim})"
  let lc = "[\{i(m)},(l1 : Value),(l2 : Value)]"
  let oldlc = "[\{i("tlsf_base(" + d + ")")},(l1 : Value),(l2 : Value)]"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let zero = "(f : Num) => (word(0) : \{w})"
  let empty = "(f : Num) => (j : Num) => (NIL : List[\{w}])"
  let bins = "tlsf_bins(\{d},word(0),\{zero},\{empty})"
  let nbins = "tlsf_bins(\{d},tlsf_push_fl(\{hdr},word(0)),tlsf_push_sb(\{hdr},\{zero}),tlsf_push_bl(\{hdr},\{m},\{empty}))"
  let top = "tlsf_top_cell(\{d})"
  let table = "pts(val(tlsf_base(\{d}))+1912,REPLICATE(264,(word(0) : Word[8])))"
  let own = (ps : Array[String]) => {
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == \{lim} && \{out}(h)"
  }
  let rest = [
    cell("word_add(" + m + ",word(4))", "word(0)"),
    "tlsf_spare(\{m},\{hdr})",
    table,
  ]
  let links = [
    cell("word_add(" + m + ",word(8))", "word(0)"),
    cell("word_add(" + m + ",word(12))", "word(0)"),
  ]
  let work = (h : String, published : Bool, t : String) => {
    "tlsf_initialize_work(\{d},\{lim},(\{h} : \{w}),\{if published { "T" } else { "F" }},(\{t} : \{w}),(fp : \{rty}))"
  }
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ lim : Num, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let ent = ent_tac([thm("tlsf_initialize_work")], [])
  let frame = own([cell(top, "word(0)")] + rest + links + [bins])
  let rawargs = [d, "(push : Num)", "(l1 : Value)", "(l2 : Value)", frame]
  let mark = inst(thm("tlsf_initialize_mark_raw"), rawargs)
  let _ = lemma(
    "tlsf_initialize_mark_work",
    "\{vars}, sl_triple_m(\{env},st(NIL,\{oldlc},\{work("word(0)",false,"word(0)")}),tlsf_initialize_mark(d,push),st(NIL,\{lc},\{work("word(2)",false,"word(0)")}),NIL)",
    seq([gen, initialize_m_conseq(mark, ent, ent)]),
  )
  let r2 = "(gs : List[Value]) => (ms : Num) => star(\{cell(m,"word(2)")},(\{frame})(gs,ms))"
  let before = inst(thm("tlsf_initialize_size_before_raw"), rawargs + [r2])
  let size = @simp.rewrite_rule(ths([@lists.append()]))(
    inst(thm("st_memory_size_at"), ["[\{i(m)}]", lc, lim, r2]),
  )
  let size = @bool.mp(
    size,
    @tactics.prove(
      @basics.dest_imp(@kernel.concl(size)).0,
      seq([gen, beta_goal(), rw(lift_rws()), @meson.meson_tac(ths([]))]),
    ),
  )
  let after = inst(thm("tlsf_initialize_size_after_raw"), rawargs + [lim])
  let bt = args_of(@kernel.concl(before), "sl_triple", 3).unwrap()
  let stt = args_of(@kernel.concl(size), "sl_triple", 3).unwrap()
  let _ = lemma(
    "tlsf_initialize_size_work",
    "\{vars}, MOD(lim,65536) == 0 → sl_triple_m(\{env},st(NIL,\{lc},\{work("word(2)",false,"word(0)")}),tlsf_initialize_size(d,push),st(NIL,\{lc},\{work(hdr,false,"word(0)")}),NIL)",
    seq([
      gen,
      @tactics.disch_tac,
      rw([thm("tlsf_initialize_size_parts")]),
      @tactics.match_mp_tac(thm("sl_seq_m")),
      @tactics.exists_tac(bt[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          initialize_m_conseq(before, ent, ent),
          seq([
            @tactics.match_mp_tac(thm("sl_seq_m")),
            @tactics.exists_tac(stt[2]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                initialize_m_conseq(size, ent_tac([], []), ent_tac([], [])),
                initialize_m_conseq(after, ent, ent),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  let topframe = own([cell(m, hdr)] + rest + [nbins])
  let topraw = inst(thm("tlsf_initialize_top_raw"), [
    d, "(push : Num)", "(l1 : Value)", "(l2 : Value)", topframe,
  ])
  let _ = lemma(
    "tlsf_initialize_top_work",
    "\{vars}, sl_triple_m(\{env},st(NIL,\{lc},\{work(hdr,true,"word(0)")}),tlsf_initialize_top(d,push),st(NIL,\{lc},\{work(hdr,true,m)}),NIL)",
    seq([gen, initialize_m_conseq(topraw, ent, ent)]),
  )
}
