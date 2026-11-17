// The mutation tails, closed over the actual compiled push function.

///|
fn prove_tlsf_ensure_tails() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let star = (ps : Array[String], frame : String) => {
    let mut o = frame
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      o = "star(\{ps[k]},\{o})"
    }
    o
  }
  let bins = "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let client = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  let m = "(m : \{w})"
  let h = "(hdr : \{w})"
  let e = "(e : \{w})"
  let r = "word_add(word_add(\{m},word(8)),tlsf_size(\{h}))"
  let slot = "tlsf_top_cell((d : \{w}))"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ hdr : \{w}, ∀ e : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ pf0 : \{w}, ∀ nf0 : \{w}, ∀ fp : \{rty}, ∀ lim2 : Num"
  let same = seq([gen, beta_goal(), strip, arw([])])
  let conseq = (
    a : Array[@kernel.Term],
    core : @tactics.Tactic,
    pre : @tactics.Tactic,
    post : @tactics.Tactic,
  ) => {
    seq([
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(a[3]),
      @tactics.exists_tac(a[5]),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([solve(core), solve(pre), solve(post), solve(same)]),
      ),
    ])
  }
  for used in [false, true] {
    let part = if used { "used" } else { "free" }
    let target = if used { r } else { m }
    let rh = if used {
      "word_or(tlsf_capacity_at((lim2 : Num),\{target}),word(2))"
    } else {
      "word_or(tlsf_capacity_at((lim2 : Num),\{target}),word_and(\{h},word(3)))"
    }
    let links = [
      cell("word_add(\{target},word(8))", "pf0"),
      cell("word_add(\{target},word(12))", "nf0"),
      bins,
    ]
    let frame = "(gs : List[Value]) => (ms : Num) => \{star(links,client)}"
    let write = inst(thm("tlsf_ensure_" + part + "_write_raw"), [
      "(d : \{w})",
      "(pop : Num)",
      "(push : Num)",
      m,
      h,
      e,
      frame,
      "(lim2 : Num)",
    ])
    let wt = args_of(@basics.dest_imp(@kernel.concl(write)).1, "sl_triple", 3).unwrap()
    let wq = args_of(wt[2], "st", 3).unwrap()
    let lc = show(wq[1])
    let r1 = show(wq[2])
    let load = @bool.spec_all(
      sym_prove(
        "tlsf_ensure_" + part + "_push_arg",
        "\{vars}, sl_triple(st(NIL,\{lc},\{r1}),[Local_get(" +
        (if used { "1" } else { "0" }) +
        ")],st([\{i(target)}],\{lc},\{r1}))",
        [],
        () => [],
      ),
    )
    let lt = args_of(@kernel.concl(load), "sl_triple", 3).unwrap()
    let extras = if used {
      [
        cell(slot, r),
        cell("m", "word_and(\{h},word(4294967293))"),
        cell("word_add(\{r},word(4))", "m"),
      ]
    } else {
      []
    }
    let fpush = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && \{star(extras,client)}(h)"
    let push = @simp.rewrite_rule(ths([@class.eta_ax()]))(
      inst(thm("tlsf_ensure_push_invoke"), [
        "(fs : List[Cl])",
        "(tabs : List[(Tab_t,List[V_ref])])",
        "(inst : Inst)",
        "(d : \{w})",
        "(push : Num)",
        target,
        lc,
        rh,
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "(pf0 : \{w})",
        "(nf0 : \{w})",
        fpush,
      ]),
    )
    let pt = args_of(@basics.dest_imp(@kernel.concl(push)).1, "sl_triple_m", 7).unwrap()
    let code = "APPEND(tlsf_ensure_" +
      part +
      "_write((d : \{w}),(pop : Num),(push : Num)),[Local_get(" +
      (if used { "1" } else { "0" }) +
      "),Call(push),Drop])"
    let lcode = "APPEND([Local_get(" +
      (if used { "1" } else { "0" }) +
      ")],[Call((push : Num)),Drop])"
    let lift = (th : @kernel.Thm) => {
      seq([
        @tactics.match_mp_tac(thm("sl_triple_m_of")),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            call_free_tac(),
            seq([
              @tactics.match_mp_tac(thm("sl_triple_l_of")),
              if @basics.is_imp(@kernel.concl(th)) {
                seq([@tactics.match_mp_tac(th), arw([])])
              } else {
                @tactics.accept_tac(th)
              },
            ]),
          ]),
        ),
      ])
    }
    let _ = lemma(
      "tlsf_ensure_" + part + "_tail_raw",
      "\{vars}, \{native} && MOD(lim2,65536) == 0 && !(\{target} == word(0)) && 16 <= val(tlsf_size(\{rh})) → sl_triple_m(fs,tabs,inst,\{show(wt[0])},\{code},\{show(pt[5])},NIL)",
      () => {
        seq([
          gen,
          strip,
          @tactics.match_mp_tac(thm("sl_seq_m")),
          @tactics.exists_tac(wt[2]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              lift(write),
              seq([
                @tactics.subst1_tac(
                  @equal.gsym(
                    @simp.rewrite_conv(ths([@lists.append()]))(tm(lcode)),
                  ),
                ),
                @tactics.match_mp_tac(thm("sl_seq_m")),
                @tactics.exists_tac(lt[2]),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    lift(load),
                    conseq(
                      pt,
                      seq([@tactics.match_mp_tac(push), arw([])]),
                      ent_tac([thm("tlsf_top_cell"), thm("tlsf_size")], []),
                      same,
                    ),
                  ]),
                ),
              ]),
            ]),
          ),
        ])
      },
    )
  }
}
