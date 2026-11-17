// Close a compiled path under the module environment and the combined invariant.
// The selected free block is detached from its bin at entry, immediately after pop.
// All scratch locals are arbitrary; only locals 0 (m) and 3 (n) are fixed.

///|
fn tlsf_split_conseq(
  path : @kernel.Thm,
  pre : @tactics.Tactic,
  post : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let tr = if @basics.is_imp(@kernel.concl(path)) {
    @basics.dest_imp(@kernel.concl(path)).1
  } else {
    @kernel.concl(path)
  }
  let a = args_of(tr, "sl_triple_g", 9).unwrap()
  let use_path = if @basics.is_imp(@kernel.concl(path)) {
    seq([
      @tactics.match_mp_tac(path),
      @simp.asm_rewrite_tac(ths([])),
      @int.asm_arith_tac,
    ])
  } else {
    @tactics.accept_tac(path)
  }
  seq([
    @tactics.match_mp_tac(thm("sl_conseq_g")),
    @tactics.exists_tac(a[5]),
    @tactics.exists_tac(a[7]),
    @tactics.exists_tac(a[8]),
    @simp.rewrite_tac(ths([@lists.length(), @arith.lt_0()])),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([solve(use_path), solve(pre), solve(post)])),
  ])
}

///|
fn prove_tlsf_split_whole() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      s = "star(\{ps[k]}, \{s})"
    }
    s
  }
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let z = i("word(0)")
  let addr = "sfunc_ind((inst : Inst), (push : Num))"
  let gspec = "tlsf_proved_spec(\{addr}, tlsf_push_code((d : \{w})), [\{z}, \{z}, \{z}], 1, 1)"
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let mark = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let topcell = cell("word_add(tlsf_base((d : " + w + ")), word(1908))", "top")
  let payload = "tlsf_bytes(val((m : \{w})) + 8, val(tlsf_size((hd : \{ht})(m))))"
  let frameps = [
    topcell,
    "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))",
    cell(
      "word_add((m : " + w + "), word(4))",
      "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
    ),
    payload,
    "tlsf_regions((m : \{w}), (zs : \{lw}), (hd : \{ht}))",
    "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))",
  ]
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(frameps)}(h)"
  let path0 = inst(thm("tlsf_split_no_remainder"), [
    gspec,
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(push : Num)",
    "(m : \{w})",
    "(n : \{w})",
    "(hd : \{ht})((m : \{w}))",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    frame,
  ])
  let path = @simp.rewrite_rule(ths([@equal.gsym(thm("tlsf_size"))]))(path0)
  let p = args_of(@basics.dest_imp(@kernel.concl(path)).1, "sl_triple_g", 9).unwrap()[5]
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, \{mark}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == V_num(ConstInt32((m : \{w}))) && EL(3, lc) == V_num(ConstInt32((n : \{w}))) && vs == NIL && ms == (lim : Num) && star(\{large}, star(\{payload}, (fp : \{rty})(gs, ms)), h)"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let cond = "\{native} && tlsf_physical_ok(d, lim, top, \{oldxs}, hd) && tlsf_bins_match(\{oldxs}, \{mark}, bl) && !tlsf_used(hd(m)) && 16 <= val(n) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) <= val(tlsf_size(hd(m))) && !word_ugt(tlsf_size(hd(m)), word_add(n, word(264)))"
  let close = inst(thm("tlsf_mark_close"), [
    "(ys : \{lw})",
    "(zs : \{lw})",
    "(m : \{w})",
    "(d : \{w})",
    "(lim : Num)",
    "(top : \{w})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})((gs : List[Value]), (ms : Num))",
  ])
  let post = seq([
    gen,
    beta_goal(),
    rw(lift_rws()),
    strip,
    @tactics.mp_tac(
      @simp.rewrite_rule(
        ths([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
      )(close),
    ),
    arw([]),
    @tactics.disch_tac,
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw(
      lift_rws() + [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")],
    ),
  ])
  let _ = lemma(
    "tlsf_split_whole",
    "\{vars}, \{cond} → sl_triple_m(fs, tabs, inst, \{show(p)}, tlsf_split_code(d, push), \{q}, NIL)",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(thm("tlsf_split_in_module")),
        arw([]),
        tlsf_split_conseq(path, ent_tac([], []), post),
      ])
    },
  )
}
