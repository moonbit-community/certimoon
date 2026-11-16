///|
fn prove_tlsf_take_regions() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let bytes4 = "star(pts((a : Num), serialise_i32((pf : \{w}))), star(pts(a + 4, serialise_i32((nf : \{w}))), tlsf_bytes(a + 8, (z : Num) - 8)))"
  let _ = lemma(
    "tlsf_payload_links",
    "∀ a : Num, ∀ z : Num, 8 <= z → tlsf_bytes(a, z) == ((h : \{heap}) => ∃ pf : \{w}, ∃ nf : \{w}, \{bytes4}(h))",
    seq([
      gen,
      @tactics.disch_tac,
      have("4 + (4 + ((z : Num) - 8)) == z", @int.asm_arith_tac),
      @tactics.mp_tac(
        inst(thm("tlsf_bytes_split"), ["(a : Num)", "4", "4 + ((z : Num) - 8)"]),
      ),
      arw(
        [
          inst(thm("tlsf_bytes_split"), ["(a : Num) + 4", "4", "(z : Num) - 8"]),
          thm("tlsf_bytes_word"),
          arith("(a : Num) + 4 + 4 == a + 8"),
        ] +
        lift_rws(),
      ),
    ]),
  )
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  let _ = lemma(
    "tlsf_focus_block",
    "\{vars}, tlsf_physical_ok(d, lim, top, \{oldxs}, hd) → tlsf_block_ok(val(m), lim, m, hd) && lim <= 4294967296",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      arw([]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_layout_members"), [
          oldxs,
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
          "(m : \{w})",
        ]),
      ),
      arw([@lists.mem_append(), @lists.mem()]),
    ]),
  )
  let _ = lemma(
    "tlsf_focus_last",
    "∀ ys : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_physical_ok(d, lim, top, APPEND(ys, [m]), hd) → top == m && tlsf_last(hd(m))",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_cut_at"), [
          "(ys : \{lw})",
          "(NIL : \{lw})",
          "(m : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.undisch_tac(
        tm(
          "tlsf_layout(tlsf_end((word(0) : \{w}), (ys : \{lw})), val((m : \{w})), (lim : Num), (top : \{w}), [(m : \{w})], (hd : \{ht}))",
        ),
      ),
      rw([thm("tlsf_layout")]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let suffix = "CONS((q : \{w}), (zs : \{lw}))"
  let nextxs = "APPEND((ys : \{lw}), CONS((m : \{w}), \{suffix}))"
  let sz = "tlsf_size((hd : \{ht})((m : \{w})))"
  let next = "word_add(word_add((m : \{w}), \{sz}), word(8))"
  let _ = lemma(
    "tlsf_focus_next",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ q : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_physical_ok(d, lim, top, \{nextxs}, hd) → q == \{next} && !tlsf_last(hd(m))",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_cut_at"), [
          "(ys : \{lw})",
          suffix,
          "(m : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.undisch_tac(
        tm(
          "tlsf_layout(tlsf_end((word(0) : \{w}), (ys : \{lw})), val((m : \{w})), (lim : Num), (top : \{w}), CONS((m : \{w}), \{suffix}), (hd : \{ht}))",
        ),
      ),
      rw([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]),
      strip,
      have(
        "val(word_add((m : \{w}), \{sz})) == val(m) + val(\{sz})",
        seq([
          @tactics.match_mp_tac(thm("tlsf_val_add_exact")),
          @int.asm_arith_tac,
        ]),
      ),
      have(
        "val(\{next}) == val(word_add((m : \{w}), \{sz})) + 8",
        seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
      ),
      arw([@equal.gsym(@words.val_eq())]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_allocated_mono",
    "∀ d : \{w}, ∀ lim : Num, ∀ m : \{w}, ∀ n : \{w}, ∀ s : \{w}, ∀ oldxs : \{lw}, ∀ oldhd : \{ht}, ∀ client : \{hprop}, ∀ h : \{heap}, val(s) <= val(n) && tlsf_allocated(d, lim, m, n, oldxs, oldhd, client, h) → tlsf_allocated(d, lim, m, s, oldxs, oldhd, client, h)",
    seq([
      gen,
      rw([thm("tlsf_allocated")]),
      strip,
      arw([]),
      seq(
        [
          "(top2 : \{w})",
          "(xs2 : \{lw})",
          "(hd2 : \{ht})",
          "(fl2 : \{w})",
          "(sb2 : (Num) -> \{w})",
          "(bl2 : (Num) -> (Num) -> \{lw})",
        ].map(x => @tactics.exists_tac(tm(x))),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}
