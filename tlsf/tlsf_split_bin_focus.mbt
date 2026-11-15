///|
fn prove_tlsf_split_bin_focus() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma("tlsf_push_bl_add", "∀ h : \{w}, ∀ r : \{w}, ∀ bl : \{bt}, tlsf_push_bl(h, r, bl) == tlsf_bin_add(bl, tlsf_level_of(h), tlsf_slot_of(h), r)", seq([
    gen, rw([@class.fun_eq_thm()]), gen, rw([thm("tlsf_push_bl"), thm("tlsf_bin_add"), thm("tlsf_upd"), thm("tlsf_level_of"), thm("tlsf_slot_of")]),
    @class.cond_cases_tac, arw([]), @class.cond_cases_tac, arw([]),
  ]))
  let _ = lemma("tlsf_push_size_cong", "∀ h : \{w}, ∀ v : \{w}, ∀ r : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, tlsf_size(h) == tlsf_size(v) → tlsf_push_fl(h, fl) == tlsf_push_fl(v, fl) && tlsf_push_sb(h, sb) == tlsf_push_sb(v, sb) && tlsf_push_bl(h, r, bl) == tlsf_push_bl(v, r, bl)", seq([
    gen, strip, rw([thm("tlsf_push_fl"), thm("tlsf_push_sb"), thm("tlsf_push_bl")]), arw([]),
  ]))
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let r = "tlsf_remainder((m : \{w}), (n : \{w}))"
  let rs = "tlsf_remainder_size((hd : \{ht})((m : \{w})), (n : \{w}))"
  let nh = "tlsf_split_headers((hd : \{ht}), (m : \{w}), (n : \{w}))"
  let marked = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let newxs = "APPEND((ys : \{lw}), CONS((m : \{w}), CONS(\{r}, (zs : \{lw}))))"
  let allvars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ hd : \{ht}, ∀ bl : \{bt}"
  let pre = "tlsf_bins_match(\{oldxs}, \{marked}, (bl : \{bt})) && !MEM(\{r}, \{oldxs}) && !(\{r} == m) && tlsf_size(n) == n && tlsf_size(\{rs}) == \{rs} && 16 <= val(\{rs})"
  let _ = lemma("tlsf_split_bins_focus", "\{allvars}, \{pre} → tlsf_bins_match(\{newxs}, \{nh}, tlsf_push_bl(\{rs}, \{r}, bl))", seq([
    gen, strip,
    @tactics.mp_tac(inst(thm("tlsf_header_class_bounds"), [rs])), arw([]), strip,
    @tactics.mp_tac(inst(thm("tlsf_taken_fields"), ["(n : \{w})"])), arw([]), strip,
    @tactics.mp_tac(inst(thm("tlsf_remainder_fields"), [rs, "(hd : \{ht})((m : \{w}))"])), arw([]), strip,
    have("(\{nh})(\{r}) == word_or(\{rs}, word_and((hd : \{ht})((m : \{w})), word(2)))", rw([thm("tlsf_split_headers"), thm("tlsf_put")])),
    have("tlsf_size((\{nh})(\{r})) == tlsf_size(\{rs})", arw([])),
    @tactics.mp_tac(inst(thm("tlsf_class_size"), ["(\{nh})(\{r})", rs])), arw([]), strip,
    rw([thm("tlsf_push_bl_add")]),
    @tactics.match_mp_tac(inst(thm("tlsf_bins_match_insert"), [oldxs, newxs, marked, nh, "(bl : \{bt})", r, "tlsf_level_of(\{rs})", "tlsf_slot_of(\{rs})"])), arw([@lists.mem_append(), @lists.mem()]),
    gen, @tactics.disch_tac, @class.asm_cases_tac(tm("(m' : \{w}) == (m : \{w})")),
    @tactics.first(@list.List([
      solve(seq([
        subst_vars(), rw([thm("tlsf_mark"), thm("tlsf_split_headers"), thm("tlsf_put")]), arw([]), @tactics.mp_tac(inst(thm("tlsf_used_store_fields"), ["(hd : \{ht})((m : \{w}))"])), arw([]), @meson.meson_tac(ths([])),
      ])),
      solve(seq([
        rw([thm("tlsf_mark"), thm("tlsf_split_headers"), thm("tlsf_put")]), arw([@lists.mem_append(), @lists.mem()]), @meson.asm_meson_tac(ths([])),
      ])),
    ])),
  ]))
}
