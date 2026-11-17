///|
fn prove_tlsf_free_pop_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let marked = "tlsf_mark((hd : \{ht}),(a : \{w}))"
  let h = "(hd : \{ht})((b : \{w}))"
  let pos = "(bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h}))"
  let old = "tlsf_bins_match((xs : \{lw}),\{marked},(bl : \{bt}))"
  let base = "\{old} && !((a : \{w}) == (b : \{w})) && MEM(b,(xs : \{lw})) && !tlsf_used(\{h})"
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ a : \{w}, ∀ b : \{w}"
  let at = "(\{marked})((b : \{w})) == \{h}"
  let point = seq([
    rw([thm("tlsf_mark"), thm("tlsf_put")]),
    @simp.asm_simp_tac(ths([])),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "tlsf_free_bin_decompose",
    "\{vars}, \{base} && 16 <= val(tlsf_size(\{h})) → (∃ us : \{lw}, ∃ vs : \{lw}, \{pos} == APPEND(us,CONS(b,vs)))",
    () => {
      seq([
        gen,
        strip,
        free_have(at, point),
        @tactics.mp_tac(inst(thm("tlsf_header_class_bounds"), [h])),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_bins_match_member"), [
            "(xs : \{lw})",
            marked,
            "(bl : \{bt})",
            "(b : \{w})",
            "tlsf_level_of(\{h})",
            "tlsf_slot_of(\{h})",
          ]),
        ),
        arw([]),
        rw([@lists.mem_append_decompose()]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let removed = "APPEND((us : \{lw}),(vs : \{lw}))"
  let _ = lemma(
    "tlsf_free_pop_bins_pair",
    "\{vars}, ∀ us : \{lw}, ∀ vs : \{lw}, \{base} && \{pos} == APPEND(us,CONS(b,vs)) → tlsf_bins_match(xs,tlsf_mark(\{marked},b),tlsf_pop_bl(\{h},bl,\{removed}))",
    () => {
      seq([
        gen,
        strip,
        free_have(at, point),
        @tactics.mp_tac(
          inst(thm("tlsf_pop_bins_match"), [
            "(xs : \{lw})",
            marked,
            "(bl : \{bt})",
            "(b : \{w})",
            "(us : \{lw})",
            "(vs : \{lw})",
          ]),
        ),
        arw([]),
      ])
    },
  )
}
