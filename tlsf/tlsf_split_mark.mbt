///|
fn prove_tlsf_split_mark() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let agree = (xs : String, nh : String) => "∀ x : \{w}, MEM(x, \{xs}) → (hd : \{ht})(x) == (\{nh})(x)"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}"
  let _ = lemma("tlsf_physical_mark", "\{vars}, tlsf_physical_ok(d, lim, top, \{oldxs}, hd) && (\{agree("(ys : " + lw + ")", "nh : " + ht)}) && (\{agree("(zs : " + lw + ")", "nh : " + ht)}) && tlsf_size(nh(m)) == tlsf_size(hd(m)) && (tlsf_last(nh(m)) == tlsf_last(hd(m))) && tlsf_used(nh(m)) → tlsf_physical_ok(d, lim, top, \{oldxs}, nh)", seq([
    gen, rw([thm("tlsf_physical_ok")]), strip,
    @tactics.mp_tac(inst(thm("tlsf_layout_cut_at"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    have("tlsf_layout(tlsf_end((word(0) : \{w}), (ys : \{lw})), val((m : \{w})), (lim : Num), (top : \{w}), CONS(m, (zs : \{lw})), (nh : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_layout_replace_head"), ["(zs : \{lw})", "tlsf_end((word(0) : \{w}), (ys : \{lw}))", "val((m : \{w}))", "(lim : Num)", "(top : \{w})", "(m : \{w})", "(hd : \{ht})", "(nh : \{ht})"])), arw([]),
    ])),
    have("tlsf_layout((word(0) : \{w}), tlsf_origin((d : \{w})), (lim : Num), (top : \{w}), \{oldxs}, (nh : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_layout_glue"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "val((m : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(nh : \{ht})"])), arw([]),
    ])),
    arw([]), @tactics.match_mp_tac(inst(thm("tlsf_coalesced_mono"), [oldxs, "(hd : \{ht})", "(nh : \{ht})"])), arw([]),
    gen, rw([@lists.mem_append(), @lists.mem()]), strip, @meson.asm_meson_tac(ths([])),
  ]))
  let distinct = lemma("tlsf_focus_distinct", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_layout(p, a, lim, top, \{oldxs}, hd) → !MEM(m, ys) && !MEM(m, zs)", seq([
    gen, @tactics.disch_tac,
    @tactics.mp_tac(inst(thm("tlsf_layout_distinct"), [oldxs, "(p : \{w})", "(a : Num)", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]),
    rw([@lists.pairwise_append(), @lists.pairwise(), @equal.gsym(@lists.all_mem()), @lists.mem()]), @meson.meson_tac(ths([])),
  ]))
  let nh = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let pmap = agree("(ys : " + lw + ")", nh)
  let smap = agree("(zs : " + lw + ")", nh)
  let rpre = "tlsf_regions((word(0) : \{w}), (ys : \{lw}), \{nh}) == tlsf_regions(word(0), ys, (hd : \{ht}))"
  let rsuf = "tlsf_regions((m : \{w}), (zs : \{lw}), \{nh}) == tlsf_regions(m, zs, (hd : \{ht}))"
  let _ = lemma("tlsf_mark_focus", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_physical_ok(d, lim, top, \{oldxs}, hd) → tlsf_physical_ok(d, lim, top, \{oldxs}, \{nh}) && \{rpre} && \{rsuf} && (\{nh})(m) == word_or(word_and(hd(m), word(4294967294)), word(1)) && tlsf_size((\{nh})(m)) == tlsf_size(hd(m)) && tlsf_used((\{nh})(m))", seq([
    gen, @tactics.disch_tac,
    have("tlsf_layout((word(0) : \{w}), tlsf_origin((d : \{w})), (lim : Num), (top : \{w}), \{oldxs}, (hd : \{ht}))", seq([
      @tactics.undisch_tac(tm("tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, (hd : \{ht}))")), rw([thm("tlsf_physical_ok")]), @meson.meson_tac(ths([])),
    ])),
    @tactics.mp_tac(inst(distinct, ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    have(pmap, seq([gen, @tactics.disch_tac, rw([thm("tlsf_mark"), thm("tlsf_put")]), @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")), arw([]), @meson.asm_meson_tac(ths([]))])),
    have(smap, seq([gen, @tactics.disch_tac, rw([thm("tlsf_mark"), thm("tlsf_put")]), @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")), arw([]), @meson.asm_meson_tac(ths([]))])),
    have("tlsf_size((\{nh})((m : \{w}))) == tlsf_size((hd : \{ht})(m)) && (tlsf_last((\{nh})(m)) == tlsf_last(hd(m))) && tlsf_used((\{nh})(m))", seq([
      rw([thm("tlsf_mark"), thm("tlsf_put")]), @tactics.accept_tac(inst(thm("tlsf_used_store_fields"), ["(hd : \{ht})((m : \{w}))"])),
    ])), @tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "/\\" { @tactics.strip_assume_tac(th) } else { @tactics.no_tac }),
    have(rpre, @tactics.accept_tac(@equal.sym(@bool.mp(inst(thm("tlsf_regions_cong"), ["(ys : \{lw})", "(word(0) : \{w})", "(hd : \{ht})", nh]), @kernel.assume_rule(tm(pmap)))))),
    have(rsuf, @tactics.accept_tac(@equal.sym(@bool.mp(inst(thm("tlsf_regions_cong"), ["(zs : \{lw})", "(m : \{w})", "(hd : \{ht})", nh]), @kernel.assume_rule(tm(smap)))))),
    have("(\{nh})((m : \{w})) == word_or(word_and((hd : \{ht})(m), word(4294967294)), word(1))", rw([thm("tlsf_mark"), thm("tlsf_put")])),
    arw([]),
    @tactics.match_mp_tac(inst(thm("tlsf_physical_mark"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(d : \{w})", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", nh])), arw([]),
  ]))
}
