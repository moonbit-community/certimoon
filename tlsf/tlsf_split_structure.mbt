///|
fn prove_tlsf_split_structure() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  def("tlsf_header", "tlsf_header((s : \{w}), (last : Bool), (used : Bool)) == word_or(s, word_or((if last { word(2) } else { word(0) }), (if used { word(1) } else { word(0) })))")
  let dist = lemma("tlsf_and_or", "∀ x : \{w}, ∀ y : \{w}, ∀ z : \{w}, word_and(word_or(x, y), z) == word_or(word_and(x, z), word_and(y, z))", seq([gen, g => @tactics.accept_tac(@words.word_bitwise_rule(g.1))(g)]))
  let assoc = lemma("tlsf_and_assoc", "∀ x : \{w}, ∀ y : \{w}, ∀ z : \{w}, word_and(word_and(x, y), z) == word_and(x, word_and(y, z))", seq([gen, g => @tactics.accept_tac(@words.word_bitwise_rule(g.1))(g)]))
  let mask = lemma("tlsf_header_masks", "∀ h : \{w}, ∀ last : Bool, ∀ used : Bool, tlsf_size(tlsf_header(tlsf_size(h), last, used)) == tlsf_size(h) && word_and(tlsf_header(tlsf_size(h), last, used), word(2)) == (if last { word(2) } else { word(0) }) && word_and(tlsf_header(tlsf_size(h), last, used), word(1)) == (if used { word(1) } else { word(0) })", seq([
    gen, @class.asm_cases_tac(tm("(last : Bool)")), @class.asm_cases_tac(tm("(used : Bool)")),
    arw([thm("tlsf_header"), thm("tlsf_size")]), @tactics.repeat_tac(@tactics.conj_tac),
    rw([dist, assoc]), @tactics.conv_tac(@words.word_reduce_conv), rw([@words.word_and_0(), @words.word_or_0()]),
  ]))
  let _ = lemma("tlsf_header_fields", "∀ h : \{w}, ∀ last : Bool, ∀ used : Bool, tlsf_size(tlsf_header(tlsf_size(h), last, used)) == tlsf_size(h) && (tlsf_last(tlsf_header(tlsf_size(h), last, used)) == last) && (tlsf_used(tlsf_header(tlsf_size(h), last, used)) == used)", seq([
    gen, rw([mask, thm("tlsf_last"), thm("tlsf_used")]),
    @class.asm_cases_tac(tm("(last : Bool)")), @class.asm_cases_tac(tm("(used : Bool)")), arw([]),
    @tactics.conv_tac(@words.word_reduce_conv), rw([]),
  ]))
  def("tlsf_end", "tlsf_end((p : \{w}), (NIL : \{lw})) == p && tlsf_end(p, CONS((m : \{w}), xs)) == tlsf_end(m, xs)")
  def("tlsf_path", "tlsf_path((NIL : \{lw}), (a : Num), (lim : Num), (hd : \{ht}), (b : Num)) == (a == b) && tlsf_path(CONS((m : \{w}), xs), a, lim, hd, b) == (tlsf_block_ok(a, lim, m, hd) && !tlsf_last(hd(m)) && tlsf_path(xs, a + 8 + val(tlsf_size(hd(m))), lim, hd, b))")
  let _ = lemma("tlsf_regions_append", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ p : \{w}, ∀ hd : \{ht}, tlsf_regions(p, APPEND(ys, zs), hd) == star(tlsf_regions(p, ys, hd), tlsf_regions(tlsf_end(p, ys), zs, hd))", seq([
    @lists.list_induct_tac, rw([@lists.append(), thm("tlsf_regions"), thm("tlsf_end"), thm("star_emp_hl")]),
    gen, arw([thm("star_assoc")]),
  ]))
  let _ = lemma("tlsf_layout_cut", "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_layout(p, a, lim, top, APPEND(ys, CONS(m, zs)), hd) == (∃ b : Num, tlsf_path(ys, a, lim, hd, b) && tlsf_layout(tlsf_end(p, ys), b, lim, top, CONS(m, zs), hd))", seq([
    @lists.list_induct_tac, rw([@lists.append(), thm("tlsf_path"), thm("tlsf_end"), thm("tlsf_layout"), @lists.not_cons_nil()]),
    gen, @simp.asm_rewrite_tac(ths([])), rw([@theorems.left_and_exists_thm(), @theorems.right_and_exists_thm()]), @tactics.try_tac(@tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv))), arw([@lists.append_eq_nil(), @lists.not_cons_nil(), thm("tlsf_layout"), @theorems.conj_assoc()]),
  ]))
  for (name, pred, tail) in [
    ("tlsf_regions_cong", "tlsf_regions((p : \{w}), xs, (hd : \{ht})) == tlsf_regions(p, xs, (nh : \{ht}))", [thm("tlsf_regions")]),
    ("tlsf_layout_cong", "tlsf_layout((p : \{w}), (a : Num), (lim : Num), (top : \{w}), xs, (hd : \{ht})) == tlsf_layout(p, a, lim, top, xs, (nh : \{ht}))", [thm("tlsf_layout"), thm("tlsf_block_ok")]),
    ("tlsf_path_cong", "tlsf_path(xs, (a : Num), (lim : Num), (hd : \{ht}), (b : Num)) == tlsf_path(xs, a, lim, (nh : \{ht}), b)", [thm("tlsf_path"), thm("tlsf_block_ok")]),
  ] {
    let vars = if name == "tlsf_regions_cong" { "∀ p : \{w}" } else if name == "tlsf_coalesced_cong" { "∀ p : \{w}" } else if name == "tlsf_path_cong" { "∀ a : Num, ∀ lim : Num, ∀ b : Num" } else { "∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}" }
    let next = "(a : Num) + 8 + val(tlsf_size((nh : \{ht})((h : \{w}))))"
    let (ihargs, eqtail) = if name == "tlsf_regions_cong" {
      (["(h : \{w})", "(hd : \{ht})", "(nh : \{ht})"], "tlsf_regions((h : \{w}), (t : \{lw}), (hd : \{ht})) == tlsf_regions(h, t, (nh : \{ht}))")
    } else if name == "tlsf_layout_cong" {
      (["(h : \{w})", next, "(lim : Num)", "(top : \{w})", "(hd : \{ht})", "(nh : \{ht})"], "tlsf_layout((h : \{w}), \{next}, (lim : Num), (top : \{w}), (t : \{lw}), (hd : \{ht})) == tlsf_layout(h, \{next}, lim, top, t, (nh : \{ht}))")
    } else {
      ([next, "(lim : Num)", "(b : Num)", "(hd : \{ht})", "(nh : \{ht})"], "tlsf_path((t : \{lw}), \{next}, (lim : Num), (hd : \{ht}), (b : Num)) == tlsf_path(t, \{next}, lim, (nh : \{ht}), b)")
    }
    let _ = lemma(name, "∀ xs : \{lw}, \{vars}, ∀ hd : \{ht}, ∀ nh : \{ht}, (∀ m : \{w}, MEM(m, xs) → hd(m) == nh(m)) → \{pred}", seq([
      @lists.list_induct_tac, rw(tail + [@lists.mem()]), gen, @tactics.disch_tac,
      have("(hd : \{ht})((h : \{w})) == (nh : \{ht})(h)", @meson.asm_meson_tac(ths([]))),
      have("∀ m : \{w}, MEM(m, (t : \{lw})) → (hd : \{ht})(m) == (nh : \{ht})(m)", @meson.asm_meson_tac(ths([]))),
      have(eqtail, seq([
        @tactics.first_x_assum(th => @tactics.match_mp_tac(inst(th, ihargs))),
        @tactics.first_assum(th => @tactics.accept_tac(th)),
      ])),
      arw([]),
    ]))
  }
  ignore(strip)
}
