///|
fn prove_tlsf_split_layout() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma("tlsf_layout_split_head", "∀ zs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_layout(p, a, lim, top, CONS(m, zs), hd) && 16 <= val(tlsf_size(nh(m))) && MOD(val(tlsf_size(nh(m))), 8) == 0 && 16 <= val(tlsf_size(nh(r))) && MOD(val(tlsf_size(nh(r))), 8) == 0 && val(r) == val(m) + 8 + val(tlsf_size(nh(m))) && val(tlsf_size(nh(m))) + 8 + val(tlsf_size(nh(r))) == val(tlsf_size(hd(m))) && !tlsf_last(nh(m)) && (tlsf_last(nh(r)) == tlsf_last(hd(m))) && (∀ x : \{w}, MEM(x, zs) → hd(x) == nh(x)) → tlsf_layout(p, a, lim, (if zs == NIL { r } else { top }), CONS(m, CONS(r, zs)), nh)", seq([
    gen,
    @simp.once_rewrite_tac(ths([thm("tlsf_layout")])),
    strip,
    have("val((m : \{w})) == (a : Num) && MOD(a, 8) == 0 && !(m == word(0)) && a + 8 + val(tlsf_size((hd : \{ht})(m))) <= (lim : Num)", seq([
      @tactics.undisch_tac(tm("tlsf_block_ok((a : Num), (lim : Num), (m : \{w}), (hd : \{ht}))")), rw([thm("tlsf_block_ok")]), @meson.meson_tac(ths([])),
    ])),
    @tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "/\\" { @tactics.strip_assume_tac(th) } else { @tactics.no_tac }),
    have("MOD(val((r : \{w})), 8) == 0", seq([
      @tactics.mp_tac(inst(@arith.mod_add_mod(), ["val((m : \{w})) + 8", "val(tlsf_size((nh : \{ht})((m : \{w}))))", "8"])),
      @tactics.mp_tac(inst(@arith.mod_add_mod(), ["val((m : \{w}))", "8", "8"])),
      @simp.asm_simp_tac(ths([])), @tactics.conv_tac(@calc_num.num_reduce_conv), @int.asm_arith_tac,
    ])),
    have("tlsf_layout((m : \{w}), (a : Num) + 8 + val(tlsf_size((hd : \{ht})(m))), (lim : Num), (top : \{w}), (zs : \{lw}), (nh : \{ht}))", seq([
      @tactics.mp_tac(inst(thm("tlsf_layout_cong"), ["(zs : \{lw})", "(m : \{w})", "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((m : \{w}))))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(nh : \{ht})"])),
      @simp.asm_simp_tac(ths([])),
    ])),
    have("(a : Num) + 8 + val(tlsf_size((nh : \{ht})((m : \{w})))) + 8 + val(tlsf_size(nh((r : \{w})))) == a + 8 + val(tlsf_size((hd : \{ht})(m)))", @int.asm_arith_tac),
    have("!((r : \{w}) == word(0))", seq([rw([@equal.gsym(@words.val_eq_0())]), @int.asm_arith_tac])),
    have("MOD((a : Num) + 8 + val(tlsf_size((nh : \{ht})((m : \{w})))), 8) == 0", seq([
      @tactics.undisch_tac(tm("MOD(val((r : \{w})), 8) == 0")), arw([]),
    ])),
    @tactics.strip_assume_tac(@bool.ispec(tm("(zs : \{lw})"), @lists.list_cases())),
    subst_vars(),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]))),
    @tactics.repeat_tac(@tactics.first_x_assum(th => if head_name(@kernel.concl(th)) == "/\\" { @tactics.strip_assume_tac(th) } else { @tactics.no_tac })),
    subst_vars(),
    arw([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]),
    @simp.asm_simp_tac(ths([])),
    @tactics.try_tac(@int.asm_arith_tac),
  ]))
  let _ = lemma("tlsf_layout_replace_head", "∀ zs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ m : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_layout(p, a, lim, top, CONS(m, zs), hd) && tlsf_size(nh(m)) == tlsf_size(hd(m)) && (tlsf_last(nh(m)) == tlsf_last(hd(m))) && (∀ x : \{w}, MEM(x, zs) → hd(x) == nh(x)) → tlsf_layout(p, a, lim, top, CONS(m, zs), nh)", seq([
    gen, rw([thm("tlsf_layout"), thm("tlsf_block_ok")]), strip, arw([]),
    @tactics.mp_tac(inst(thm("tlsf_layout_cong"), ["(zs : \{lw})", "(m : \{w})", "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((m : \{w}))))", "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(nh : \{ht})"])),
    @simp.asm_simp_tac(ths([])),
  ]))
}
