///|
fn prove_tlsf_split_physical() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ground = @tactics.then_tac(@tactics.pop_assum_list(all => seq(all.to_array().filter(th => !@basics.is_forall(@kernel.concl(th))).map(@tactics.assume_tac))), @meson.asm_meson_tac(ths([])))
  let _ = lemma("tlsf_mem_hd", "∀ xs : \{lw}, !(xs == NIL) → MEM(HD(xs), xs)", seq([
    @tactics.gen_tac, @tactics.struct_cases_tac(@bool.ispec(tm("(xs : \{lw})"), @lists.list_cases())), rw([@lists.hd(), @lists.mem()]),
  ]))
  let _ = lemma("tlsf_coalesced_suffix", "∀ ys : \{lw}, ∀ xs : \{lw}, ∀ hd : \{ht}, tlsf_coalesced(APPEND(ys, xs), hd) → tlsf_coalesced(xs, hd)", seq([
    @lists.list_induct_tac, rw([@lists.append(), thm("tlsf_coalesced")]), gen, strip,
    @tactics.first_x_assum(th => @tactics.match_mp_tac(inst(th, ["(xs : \{lw})", "(hd : \{ht})"]))), arw([]),
  ]))
  let cut_at = lemma("tlsf_layout_cut_at", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_layout(p, a, lim, top, APPEND(ys, CONS(m, zs)), hd) → tlsf_path(ys, a, lim, hd, val(m)) && tlsf_layout(tlsf_end(p, ys), val(m), lim, top, CONS(m, zs), hd)", seq([
    gen, @tactics.disch_tac,
    @tactics.mp_tac(inst(thm("tlsf_layout_cut"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(p : \{w})", "(a : Num)", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    have("val((m : \{w})) == (b : Num)", seq([
      @tactics.undisch_tac(tm("tlsf_layout(tlsf_end((p : \{w}), (ys : \{lw})), (b : Num), (lim : Num), (top : \{w}), CONS((m : \{w}), (zs : \{lw})), (hd : \{ht}))")),
      rw([thm("tlsf_layout"), thm("tlsf_block_ok")]), @meson.meson_tac(ths([])),
    ])), subst_vars(), arw([]),
  ]))
  let glue = lemma("tlsf_layout_glue", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ b : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_path(ys, a, lim, hd, b) && (∀ x : \{w}, MEM(x, ys) → hd(x) == nh(x)) && tlsf_layout(tlsf_end(p, ys), b, lim, top, CONS(m, zs), nh) → tlsf_layout(p, a, lim, top, APPEND(ys, CONS(m, zs)), nh)", seq([
    gen, strip, rw([thm("tlsf_layout_cut")]), @tactics.exists_tac(tm("(b : Num)")),
    @tactics.mp_tac(inst(thm("tlsf_path_cong"), ["(ys : \{lw})", "(a : Num)", "(lim : Num)", "(b : Num)", "(hd : \{ht})", "(nh : \{ht})"])), @simp.asm_simp_tac(ths([])),
  ]))
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let newxs = "APPEND((ys : \{lw}), CONS((m : \{w}), CONS((r : \{w}), (zs : \{lw}))))"
  let newtop = "(if (zs : \{lw}) == NIL { (r : \{w}) } else { (top : \{w}) })"
  let agree = (xs : String) => "∀ x : \{w}, MEM(x, \{xs}) → (hd : \{ht})(x) == (nh : \{ht})(x)"
  let nm = "val(tlsf_size((nh : \{ht})((m : \{w}))))"
  let nr = "val(tlsf_size((nh : \{ht})((r : \{w}))))"
  let fields = "16 <= \{nm} && MOD(\{nm}, 8) == 0 && 16 <= \{nr} && MOD(\{nr}, 8) == 0 && val((r : \{w})) == val((m : \{w})) + 8 + \{nm} && \{nm} + 8 + \{nr} == val(tlsf_size((hd : \{ht})(m))) && !tlsf_last(nh(m)) && (tlsf_last(nh(r)) == tlsf_last(hd(m)))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}"
  let _ = lemma("tlsf_physical_split", "\{vars}, tlsf_physical_ok(d, lim, top, \{oldxs}, hd) && !tlsf_used(hd(m)) && tlsf_used(nh(m)) && (\{agree("(ys : " + lw + ")")}) && (\{agree("(zs : " + lw + ")")}) && \{fields} → tlsf_physical_ok(d, lim, \{newtop}, \{newxs}, nh)", seq([
    gen, rw([thm("tlsf_physical_ok")]), strip,
    @tactics.mp_tac(inst(cut_at, ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    have("tlsf_layout(tlsf_end((word(0) : \{w}), (ys : \{lw})), val((m : \{w})), (lim : Num), \{newtop}, CONS(m, CONS((r : \{w}), (zs : \{lw}))), (nh : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_layout_split_head"), ["(zs : \{lw})", "tlsf_end((word(0) : \{w}), (ys : \{lw}))", "val((m : \{w}))", "(lim : Num)", "(top : \{w})", "(m : \{w})", "(r : \{w})", "(hd : \{ht})", "(nh : \{ht})"])), arw([]),
    ])),
    have("tlsf_layout((word(0) : \{w}), tlsf_origin((d : \{w})), (lim : Num), \{newtop}, \{newxs}, (nh : \{ht}))", seq([
      @tactics.match_mp_tac(inst(glue, ["(ys : \{lw})", "CONS((r : \{w}), (zs : \{lw}))", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "val((m : \{w}))", "(lim : Num)", newtop, "(hd : \{ht})", "(nh : \{ht})"])), arw([]),
    ])),
    have("tlsf_coalesced(\{oldxs}, (nh : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_coalesced_mono"), [oldxs, "(hd : \{ht})", "(nh : \{ht})"])), arw([]), gen, rw([@lists.mem_append(), @lists.mem()]), strip,
      @meson.asm_meson_tac(ths([])),
    ])),
    have("tlsf_coalesced(CONS((m : \{w}), (zs : \{lw})), (hd : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_coalesced_suffix"), ["(ys : \{lw})", "CONS((m : \{w}), (zs : \{lw}))", "(hd : \{ht})"])), arw([]),
    ])),
    have("(zs : \{lw}) == NIL || tlsf_used((hd : \{ht})(HD(zs)))", seq([
      @tactics.undisch_tac(tm("tlsf_coalesced(CONS((m : \{w}), (zs : \{lw})), (hd : \{ht}))")), rw([thm("tlsf_coalesced")]), arw([]), @meson.meson_tac(ths([])),
    ])),
    have("(zs : \{lw}) == NIL || tlsf_used((nh : \{ht})(HD(zs)))", seq([
      @tactics.assume_tac(inst(thm("tlsf_mem_hd"), ["(zs : \{lw})"])),
      @tactics.first_x_assum(th => @tactics.assume_tac(@bool.spec(tm("HD((zs : \{lw}))"), th))), ground,
    ])),
    arw([@lists.append_eq_nil(), @lists.not_cons_nil()]),
    @tactics.match_mp_tac(inst(thm("tlsf_coalesced_splice"), ["(ys : \{lw})", "(m : \{w})", "(r : \{w})", "(zs : \{lw})", "(nh : \{ht})"])), arw([]),
  ]))
}
