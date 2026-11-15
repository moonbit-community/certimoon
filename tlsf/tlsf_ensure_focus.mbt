///|
fn prove_tlsf_ensure_focus() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let xs = "APPEND((ys : \{lw}),[(m : \{w})])"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),(m : \{w}),\{xs},(hd : \{ht}))"
  let lay = "tlsf_layout((word(0) : \{w}),tlsf_origin((d : \{w})),(lim : Num),(m : \{w}),\{xs},(hd : \{ht}))"
  let block = "tlsf_block_ok(val((m : \{w})),(lim : Num),(m : \{w}),(hd : \{ht}))"
  let facts = "(lim : Num) <= 4294967296 && MOD(lim,65536) == 0 && 0 < val((m : \{w})) && MOD(val(m),8) == 0 && 16 <= val(tlsf_size((hd : \{ht})(m))) && val(m)+8+val(tlsf_size(hd(m))) == lim && tlsf_last(hd(m)) && !MEM(m,(ys : \{lw}))"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}"
  let _ = lemma(
    "tlsf_ensure_top_facts",
    "\{vars}, \{old} → \{facts}",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_block"), [
          "(ys : \{lw})",
          "(NIL : \{lw})",
          "(m : \{w})",
          "(d : \{w})",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      have(
        lay,
        seq([
          @tactics.undisch_tac(tm(old)),
          rw([thm("tlsf_physical_ok")]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_focus_distinct"), [
          "(ys : \{lw})",
          "(NIL : \{lw})",
          "(m : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_cut_at"), [
          "(ys : \{lw})",
          "(NIL : \{lw})",
          "(m : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.undisch_tac(
        tm(
          "tlsf_layout(tlsf_end((word(0) : \{w}),(ys : \{lw})),val((m : \{w})),(lim : Num),m,[m],(hd : \{ht}))",
        ),
      ),
      rw([thm("tlsf_layout"), thm("tlsf_block_ok")]),
      strip,
      have(
        "MOD((lim : Num),65536) == 0",
        seq([
          @tactics.undisch_tac(tm(old)),
          rw([thm("tlsf_physical_ok")]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      have(
        "0 < val((m : \{w}))",
        seq([
          @tactics.undisch_tac(tm(block)),
          rw([thm("tlsf_block_ok"), @equal.gsym(@words.val_eq_0())]),
          @int.arith_tac,
        ]),
      ),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_ensure_old_bound",
    "\{vars}, ∀ x : \{w}, \{old} && MEM(x,\{xs}) → val(x) < lim",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_members"), [
          xs,
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
          "(x : \{w})",
        ]),
      ),
      arw([]),
      rw([thm("tlsf_block_ok")]),
      strip,
      @int.asm_arith_tac,
    ]),
  )
}
