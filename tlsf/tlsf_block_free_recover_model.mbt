// With no live or cached blocks, the local free list owns one link for
// every canonical slot, irrespective of the order in which blocks were freed.

///|
fn prove_tlsf_block_free_recover_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ft = "(\{w}) -> \{hprop}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_small_hlist_slots",
    "∀ n : Num, ∀ ff : \{ft}, ∀ p : \{w}, ∀ s : Num, tlsf_small_hlist(ff,tlsf_small_slots(p,s,n)) == tlsf_istar((i : Num) => ff(tlsf_small_slot(p,s,i)),n)",
    seq([
      @nums.induct_tac,
      rw(
        [
          thm("tlsf_small_slots"),
          thm("tlsf_small_hlist"),
          thm("tlsf_istar"),
          thm("tlsf_small_hlist_append"),
        ] +
        ac,
      ),
      gen,
      arw(ac),
    ]),
  )
  let args = [
    "(lim : Num)",
    "(p : " + w + ")",
    "(cap : Num)",
    "(s : Num)",
    "(loc : " + lw + ")",
    "(NIL : " + lw + ")",
    "(NIL : " + lw + ")",
  ]
  let ok = "tlsf_small_page_ok(" + args.join(",") + ")"
  let canonical = "tlsf_small_slots((p : \{w}),(s : Num),tlsf_small_total(s))"
  let _ = lemma(
    "tlsf_small_reclaim_list",
    "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ ff : \{ft}, \{ok} → tlsf_small_hlist(ff,loc) == tlsf_istar((i : Num) => ff(tlsf_small_slot(p,s,i)),tlsf_small_total(s))",
    seq([
      gen,
      @tactics.disch_tac,
      free_have(
        "tlsf_small_partition((p : \{w}),(s : Num),(loc : \{lw}),(NIL : \{lw}),(NIL : \{lw}))",
        seq([
          @tactics.undisch_tac(tm(ok)),
          rw([thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      free_have(
        "∀ i : Num, ∀ j : Num, i < tlsf_small_total((s : Num)) && j < tlsf_small_total(s) && tlsf_small_slot((p : \{w}),s,i) == tlsf_small_slot(p,s,j) → i == j",
        seq([
          gen,
          strip,
          @tactics.mp_tac(
            inst(
              thm("tlsf_small_slot_injective"),
              args + ["(i : Num)", "(j : Num)"],
            ),
          ),
          arw([]),
          small_meson(ths([])),
        ]),
      ),
      g => {
        @tactics.assume_tac(
          block_under(
            inst(thm("tlsf_small_slots_counts"), [
              "tlsf_small_total((s : Num))",
              "(p : " + w + ")",
              "(s : Num)",
            ]),
            g,
          ),
        )(g)
      },
      free_have(
        "∀ b : \{w}, tlsf_count(b,(loc : \{lw})) == (if MEM(b,\{canonical}) { 1 } else { 0 })",
        seq([
          gen,
          @tactics.mp_tac(
            inst(thm("tlsf_small_partition_counts"), [
              "(p : " + w + ")",
              "(s : Num)",
              "(loc : " + lw + ")",
              "(NIL : " + lw + ")",
              "(NIL : " + lw + ")",
              "(b : " + w + ")",
            ]),
          ),
          arw([thm("tlsf_small_count_nil"), @arith.add_clauses()]),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_hlist_permutation"), [
          canonical,
          "(ff : " + ft + ")",
          "(loc : " + lw + ")",
        ]),
      ),
      arw([]),
      rw([@class.cond_id()]),
      @tactics.first(
        @list.List([
          solve(
            seq([rw([thm("tlsf_small_hlist_slots")]), small_meson(ths([]))]),
          ),
          solve(
            seq([
              free_have(
                "∀ q : \{w}, MEM(q,\{canonical}) → tlsf_count(q,\{canonical}) == 1",
                seq([gen, @tactics.disch_tac, arw([])]),
              ),
              arw([thm("tlsf_small_hlist_slots")]),
              small_meson(ths([])),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
