///|
fn prove_tlsf_split_focus() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let r = "tlsf_remainder((m : \{w}), (n : \{w}))"
  let rs = "tlsf_remainder_size((hd : \{ht})((m : \{w})), (n : \{w}))"
  let nh = "tlsf_split_headers((hd : \{ht}), (m : \{w}), (n : \{w}))"
  let newxs = "APPEND((ys : \{lw}), CONS((m : \{w}), CONS(\{r}, (zs : \{lw}))))"
  let newtop = "(if (zs : \{lw}) == NIL { \{r} } else { (top : \{w}) })"
  let agree = (xs : String) => "∀ x : \{w}, MEM(x, \{xs}) → (hd : \{ht})(x) == (\{nh})(x)"
  let pre = "tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, (hd : \{ht})) && !tlsf_used(hd(m)) && 16 <= val((n : \{w})) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) + 264 < val(tlsf_size(hd(m)))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  let geometry = "val(\{r}) == val((m : \{w})) + 8 + val((n : \{w})) && !(\{r} == word(0)) && !(\{r} == m) && val(\{rs}) == val(tlsf_size((hd : \{ht})(m))) - val(n) - 8 && 16 <= val(\{rs}) && MOD(val(\{rs}), 8) == 0 && tlsf_size(n) == n && tlsf_size(\{rs}) == \{rs} && val(n) + 8 + val(\{rs}) == val(tlsf_size(hd(m)))"
  let geom = lemma("tlsf_split_focus_geometry", "\{vars}, \{pre} → \{geometry} && !MEM(\{r}, \{oldxs}) && !MEM(m, ys) && !MEM(m, zs)", seq([
    gen, strip,
    have("tlsf_layout((word(0) : \{w}), tlsf_origin((d : \{w})), (lim : Num), (top : \{w}), \{oldxs}, (hd : \{ht})) && (lim : Num) <= 4294967296", seq([
      @tactics.undisch_tac(tm("tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, (hd : \{ht}))")), rw([thm("tlsf_physical_ok")]), @meson.meson_tac(ths([])),
    ])), @tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "/\\" { @tactics.strip_assume_tac(th) } else { @tactics.no_tac }),
    have("tlsf_block_ok(val((m : \{w})), (lim : Num), m, (hd : \{ht}))", seq([
      @tactics.match_mp_tac(inst(thm("tlsf_layout_members"), [oldxs, "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(m : \{w})"])), arw([@lists.mem_append(), @lists.mem()]),
    ])),
    @tactics.mp_tac(inst(thm("tlsf_split_bounds"), ["(m : \{w})", "(n : \{w})", "(hd : \{ht})", "(lim : Num)"])), arw([]), strip,
    @tactics.mp_tac(inst(thm("tlsf_focus_distinct"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    arw([]), @tactics.match_mp_tac(inst(thm("tlsf_layout_interior"), [oldxs, "(word(0) : \{w})", "tlsf_origin((d : \{w}))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(m : \{w})", r])),
    arw([@lists.mem_append(), @lists.mem()]), @int.asm_arith_tac,
  ]))
  let post = "tlsf_physical_ok((d : \{w}), (lim : Num), \{newtop}, \{newxs}, \{nh}) && (\{agree("(ys : " + lw + ")")}) && (\{agree("(zs : " + lw + ")")}) && (\{nh})(m) == word_or(n, word(1)) && (\{nh})(\{r}) == word_or(\{rs}, word_and(hd(m), word(2)))"
  let _ = lemma("tlsf_split_focus", "\{vars}, \{pre} → \{post}", seq([
    gen, strip, @tactics.mp_tac(inst(geom, ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(n : \{w})", "(d : \{w})", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    have(agree("(ys : " + lw + ")"), seq([
      gen, @tactics.disch_tac,
      have("!((x : \{w}) == (m : \{w})) && !(x == \{r})", @meson.asm_meson_tac(ths([@lists.mem_append(), @lists.mem()]))),
      rw([thm("tlsf_split_headers"), thm("tlsf_put")]), arw([]),
    ])),
    have(agree("(zs : " + lw + ")"), seq([
      gen, @tactics.disch_tac,
      have("!((x : \{w}) == (m : \{w})) && !(x == \{r})", @meson.asm_meson_tac(ths([@lists.mem_append(), @lists.mem()]))),
      rw([thm("tlsf_split_headers"), thm("tlsf_put")]), arw([]),
    ])),
    have("(\{nh})((m : \{w})) == word_or((n : \{w}), word(1)) && (\{nh})(\{r}) == word_or(\{rs}, word_and((hd : \{ht})(m), word(2)))", seq([rw([thm("tlsf_split_headers"), thm("tlsf_put")]), arw([]), @meson.asm_meson_tac(ths([]))])), @tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "/\\" { @tactics.strip_assume_tac(th) } else { @tactics.no_tac }),
    @tactics.mp_tac(inst(thm("tlsf_taken_fields"), ["(n : \{w})"])), arw([]), strip,
    @tactics.mp_tac(inst(thm("tlsf_remainder_fields"), [rs, "(hd : \{ht})((m : \{w}))"])), arw([]), strip,
    @tactics.pop_assum_list(all => seq(all.to_array().filter(th => !@basics.aconv(@kernel.concl(th), tm("val(\{rs}) == val(tlsf_size((hd : \{ht})((m : \{w})))) - val((n : \{w})) - 8"))).map(@tactics.assume_tac))),
    arw([]), @tactics.match_mp_tac(inst(thm("tlsf_physical_split"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", r, "(d : \{w})", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", nh])), arw([]),
    have("MOD(val((n : \{w})), 8) == 0", seq([@tactics.match_mp_tac(thm("tlsf_mod16_8")), arw([])])), @int.asm_arith_tac,
  ]))
}
