///|
fn prove_tlsf_ensure_bin_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let marked = "tlsf_mark((hd : \{ht}),(m : \{w}))"
  let h = "(nh : \{ht})((m : \{w}))"
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}"
  let _ = lemma(
    "tlsf_extend_bins",
    "\{vars}, tlsf_bins_match(xs,\{marked},bl) && MEM(m,xs) && !tlsf_used(\{h}) && 16 <= val(tlsf_size(\{h})) && (∀ x : \{w}, !(x == m) → hd(x) == nh(x)) → tlsf_bins_match(xs,nh,tlsf_push_bl(\{h},m,bl))",
    seq([
      gen,
      strip,
      @tactics.assume_tac(
        inst(thm("tlsf_mark_used"), ["(hd : \{ht})", "(m : \{w})"]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_header_class_bounds"), [h])),
      arw([]),
      strip,
      rw([thm("tlsf_push_bl_add")]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_bins_match_publish"), [
          "(xs : \{lw})",
          "(xs : \{lw})",
          marked,
          "(nh : \{ht})",
          "(bl : \{bt})",
          "(m : \{w})",
          "tlsf_level_of(\{h})",
          "tlsf_slot_of(\{h})",
        ]),
      ),
      arw([]),
      @tactics.x_gen_tac(tm("(x : \{w})")),
      @tactics.disch_tac,
      @tactics.first_x_assum(th => {
        if @basics.is_forall(@kernel.concl(th)) {
          @tactics.assume_tac(@bool.spec(tm("(x : \{w})"), th))
        } else {
          @tactics.no_tac
        }
      }),
      have(
        "(hd : \{ht})((x : \{w})) == (nh : \{ht})(x)",
        @meson.asm_meson_tac(ths([])),
      ),
      rw([thm("tlsf_mark"), thm("tlsf_put")]),
      arw([]),
    ]),
  )
  let r = "(r : \{w})"
  // Write the nested update explicitly to keep both changed addresses visible.
  let a = "tlsf_put(tlsf_put((hd : \{ht}),(m : \{w}),word_and(hd(m),word(4294967293))),\{r},(rh : \{w}))"
  let _ = lemma(
    "tlsf_append_bins",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, ∀ r : \{w}, ∀ rh : \{w}, tlsf_bins_match(xs,hd,bl) && tlsf_used(hd(m)) && !MEM(r,xs) && !tlsf_used(rh) && 16 <= val(tlsf_size(rh)) → tlsf_bins_match(APPEND(xs,[r]),\{a},tlsf_push_bl(rh,r,bl))",
    seq([
      gen,
      strip,
      have(
        "!((r : \{w}) == (m : \{w})) || !MEM((m : \{w}),(xs : \{lw}))",
        @meson.asm_meson_tac(ths([])),
      ),
      @tactics.mp_tac(inst(thm("tlsf_header_class_bounds"), ["(rh : \{w})"])),
      arw([]),
      strip,
      rw([thm("tlsf_push_bl_add")]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_bins_match_publish"), [
          "(xs : \{lw})",
          "APPEND((xs : \{lw}),[(r : \{w})])",
          "(hd : \{ht})",
          a,
          "(bl : \{bt})",
          r,
          "tlsf_level_of((rh : \{w}))",
          "tlsf_slot_of((rh : \{w}))",
        ]),
      ),
      arw([@lists.mem_append(), @lists.mem(), thm("tlsf_put")]),
      @tactics.x_gen_tac(tm("(x : \{w})")),
      @tactics.disch_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")),
        @list.List([
          seq([
            subst_vars(),
            arw([thm("tlsf_put")]),
            @tactics.mp_tac(
              inst(thm("tlsf_clear_last_fields"), ["(hd : \{ht})((m : \{w}))"]),
            ),
            arw([]),
            @meson.meson_tac(ths([])),
          ]),
          seq([
            arw([thm("tlsf_put"), @lists.mem_append(), @lists.mem()]),
            @meson.asm_meson_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}
