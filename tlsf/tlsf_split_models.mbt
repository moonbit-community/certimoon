///|
fn prove_tlsf_split_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let word : @tactics.Tactic = g => @tactics.accept_tac(@words.word_rule(g.1))(g)
  def("tlsf_put", "tlsf_put((hd : \{ht}), (m : \{w}), (v : \{w}), (x : \{w})) == (if x == m { v } else { hd(x) })")
  def("tlsf_mark", "tlsf_mark((hd : \{ht}), (m : \{w})) == tlsf_put(hd, m, word_or(word_and(hd(m), word(4294967294)), word(1)))")
  def("tlsf_remainder", "tlsf_remainder((m : \{w}), (n : \{w})) == word_add(n, word_add(m, word(8)))")
  def("tlsf_remainder_size", "tlsf_remainder_size((h : \{w}), (n : \{w})) == word_sub(word_sub(tlsf_size(h), n), word(8))")
  def("tlsf_split_headers", "tlsf_split_headers((hd : \{ht}), (m : \{w}), (n : \{w})) == tlsf_put(tlsf_put(hd, m, word_or(n, word(1))), tlsf_remainder(m, n), word_or(tlsf_remainder_size(hd(m), n), word_and(hd(m), word(2))))")
  def("tlsf_bin_add", "tlsf_bin_add((bl : \{bt}), (f : Num), (j : Num), (m : \{w}), (i : Num), (k : Num)) == (if i == f && k == j { CONS(m, bl(i)(k)) } else { bl(i)(k) })")
  let _ = lemma("tlsf_size_mask_id", "∀ h : \{w}, tlsf_size(tlsf_size(h)) == tlsf_size(h)", seq([gen, rw([thm("tlsf_size")]), word]))
  let size_val = lemma("tlsf_size_value", "∀ h : \{w}, val(tlsf_size(h)) == 4 * DIV(val(h), 4)", seq([
    gen, rw([thm("tlsf_size")]), @tactics.accept_tac(@equal.conv_rule(@words.word_reduce_conv, @equal.conv_rule(@calc_num.num_reduce_conv, inst(@words.val_word_and_not_mask_word(), ["(h : \{w})", "2"])))),
  ]))
  let clean = lemma("tlsf_size_clean", "∀ h : \{w}, (tlsf_size(h) == h) == (MOD(val(h), 4) == 0)", seq([
    gen, rw([@equal.gsym(@words.val_eq()), size_val]),
    @tactics.mp_tac(inst(@arith.division(), ["val((h : \{w}))", "4"])), @tactics.conv_tac(@calc_num.num_reduce_conv), @int.arith_tac,
  ]))
  let rem = "tlsf_remainder_size((h : \{w}), (n : \{w}))"
  let z = "val(tlsf_size((h : \{w})))"
  let nv = "val((n : \{w}))"
  let _ = lemma("tlsf_remainder_mask", "∀ h : \{w}, ∀ n : \{w}, tlsf_size(n) == n && val(n) + 8 <= val(tlsf_size(h)) → tlsf_size(tlsf_remainder_size(h, n)) == tlsf_remainder_size(h, n)", seq([
    gen, strip,
    have("\{nv} <= \{z}", @int.asm_arith_tac),
    have("val(word_sub(tlsf_size((h : \{w})), (n : \{w}))) == \{z} - \{nv}", seq([rw([@words.val_word_sub_cases()]), arw([])])),
    have("8 <= val(word_sub(tlsf_size((h : \{w})), (n : \{w})))", @int.asm_arith_tac),
    have("8 <= \{z} - \{nv}", @int.asm_arith_tac),
    have("val(\{rem}) == \{z} - \{nv} - 8", seq([rw([thm("tlsf_remainder_size"), @words.val_word_sub_cases(), @words.val_word(), @words.dimindex_32()]), @tactics.conv_tac(@calc_num.num_reduce_conv), arw([])])),
    have("\{nv} == 4 * DIV(\{nv}, 4)", seq([@tactics.mp_tac(inst(size_val, ["(n : \{w})"])), arw([])])),
    have("\{z} == 4 * DIV(\{z}, 4)", seq([@tactics.mp_tac(inst(size_val, ["tlsf_size((h : \{w}))"])), rw([thm("tlsf_size_mask_id")])])),
    have("DIV(\{nv}, 4) + 2 <= DIV(\{z}, 4)", @int.asm_arith_tac),
    have("val(\{rem}) == 4 * (DIV(\{z}, 4) - DIV(\{nv}, 4) - 2)", seq([rw([@arith.left_sub_distrib()]), @int.asm_arith_tac])),
    rw([clean]),
    @tactics.first_x_assum(th => if @basics.aconv(@equal.lhs(@kernel.concl(th)), tm("val(\{rem})")) && head_name(@equal.rhs(@kernel.concl(th))) == "*" { @tactics.subst1_tac(th) } else { @tactics.no_tac }),
    rw([@arith.mod_mult()]),
  ]))
  let _ = lemma("tlsf_header_fields_clean", "∀ h : \{w}, ∀ last : Bool, ∀ used : Bool, tlsf_size(h) == h → tlsf_size(tlsf_header(h, last, used)) == h && (tlsf_last(tlsf_header(h, last, used)) == last) && (tlsf_used(tlsf_header(h, last, used)) == used)", seq([
    gen, @tactics.disch_tac, @tactics.mp_tac(inst(thm("tlsf_header_fields"), ["(h : \{w})", "(last : Bool)", "(used : Bool)"])), arw([]),
  ]))
  let _ = lemma("tlsf_class_size", "∀ h : \{w}, ∀ v : \{w}, tlsf_size(h) == tlsf_size(v) → tlsf_level_of(h) == tlsf_level_of(v) && tlsf_slot_of(h) == tlsf_slot_of(v)", seq([gen, rw([thm("tlsf_level_of"), thm("tlsf_slot_of")]), @meson.meson_tac(ths([]))]))
  let _ = lemma("tlsf_count_cons", "∀ m : \{w}, ∀ a : \{w}, ∀ xs : \{lw}, tlsf_count(m, CONS(a, xs)) == (if m == a { SUC(tlsf_count(m, xs)) } else { tlsf_count(m, xs) })", seq([
    gen, rw([thm("tlsf_count"), @lists.filter()]), @class.asm_cases_tac(tm("(m : \{w}) == (a : \{w})")), arw([@lists.length()]),
  ]))
}
