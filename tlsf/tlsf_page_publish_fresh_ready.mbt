// The complete initialized slot list is a valid local-only page before
// publication, even though its concrete used/prev words are still arbitrary.

///|
fn prove_tlsf_page_publish_fresh_ready() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_page_publish_count_reverse",
    "∀ xs : " +
    lw +
    ", ∀ b : " +
    w +
    ", tlsf_count(b,REVERSE(xs)) == tlsf_count(b,xs)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          @lists.reverse(),
          thm("tlsf_small_count_nil"),
          thm("tlsf_small_count_append"),
          thm("tlsf_small_count_cons"),
        ]),
        gen,
        arw([thm("tlsf_small_count_nil")]),
        @int.arith_tac,
      ])
    },
  )
  let p = "(p : " + w + ")"
  let s = "(s : Num)"
  let cap = "(cap : Num)"
  let geom = "tlsf_page_allocate_geometry(" + p + "," + cap + "," + s + ")"
  let slots = "REVERSE(tlsf_small_slots(" +
    p +
    "," +
    s +
    ",tlsf_small_total(s)))"
  let _ = lemma(
    "tlsf_page_publish_fresh_partition",
    "∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, " +
    geom +
    " → tlsf_small_partition(p,s," +
    slots +
    ",NIL,NIL)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have(
          "∀ i : Num, ∀ j : Num, i < tlsf_small_total(" +
          s +
          ") && j < tlsf_small_total(s) && tlsf_small_slot(" +
          p +
          ",s,i) == tlsf_small_slot(p,s,j) → i == j",
          seq([
            gen,
            strip,
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_page_allocate_bounds"), [
                    p, cap, s, "(i : Num)",
                  ]),
                  g,
                ),
              )(g)
            },
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_page_allocate_bounds"), [
                    p, cap, s, "(j : Num)",
                  ]),
                  g,
                ),
              )(g)
            },
            @tactics.undisch_tac(
              tm(
                "tlsf_small_slot(" +
                p +
                "," +
                s +
                ",(i : Num)) == tlsf_small_slot(p,s,(j : Num))",
              ),
            ),
            rw([@equal.gsym(@words.val_eq())]),
            arw([@arith.eq_add_lcancel(), @arith.eq_mult_lcancel()]),
            @int.arith_tac,
          ]),
        ),
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_small_slots_counts"), [
                "tlsf_small_total(" + s + ")",
                p,
                s,
              ]),
              g,
            ),
          )(g)
        },
        rw([
          thm("tlsf_small_partition"),
          @lists.append(),
          @lists.append_nil(),
          @lists.length_reverse(),
          thm("tlsf_small_slots_length"),
          thm("tlsf_small_used"),
          @lists.length(),
          @arith.add_clauses(),
          thm("tlsf_page_publish_count_reverse"),
        ]),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_page_publish_fresh_ready",
    "∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, ∀ lim : Num, " +
    geom +
    " && val(p)+8+cap <= lim && lim <= 4294967296 → tlsf_small_page_ok(lim,p,cap,s," +
    slots +
    ",NIL,NIL)",
    () => {
      seq([
        gen,
        strip,
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_fresh_partition"), [p, cap, s]),
              g,
            ),
          )(g)
        },
        @tactics.undisch_tac(tm(geom)),
        rw([thm("tlsf_page_allocate_geometry"), thm("tlsf_small_page_ok")]),
        strip,
        arw([]),
      ])
    },
  )
}
