// A class-cache entry belongs to exactly one physical page. This is derived
// from the chain and the page partition, rather than assumed about the cache.

///|
fn prove_tlsf_malloc_cached_owner() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let model = page_model_variables()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let q = "(q : " + w + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_cached_unique",
    "∀ p : " +
    w +
    ", ∀ s : Num, ∀ loc : " +
    lw +
    ", ∀ cached : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", tlsf_small_partition(p,s,loc,cached,live) && MEM(b,cached) → MEM(b,tlsf_small_slots(p,s,tlsf_small_total(s))) && tlsf_count(b,cached) == 1 && !MEM(b,live) && !MEM(b,loc)",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "0 < tlsf_count(" + b + ",(cached : " + lw + "))",
          seq([rw([@equal.gsym(thm("tlsf_count_member"))]), arw([])]),
        ),
        @class.asm_cases_tac(
          tm(
            "MEM(" +
            b +
            ",tlsf_small_slots(" +
            p +
            ",(s : Num),tlsf_small_total(s)))",
          ),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_small_partition_counts"), [
            p,
            "(s : Num)",
            "(loc : " + lw + ")",
            "(cached : " + lw + ")",
            "(live : " + lw + ")",
            b,
          ]),
        ),
        arw([@equal.gsym(thm("tlsf_count_zero"))]),
        @int.asm_arith_tac,
      ])
    },
  )
  let part = "tlsf_small_partition(" +
    p +
    "," +
    a[9] +
    "(" +
    p +
    ")," +
    a[10] +
    "(" +
    p +
    ")," +
    a[11] +
    "(" +
    p +
    ")," +
    a[12] +
    "(" +
    p +
    "))"
  let cond = block_backing(a) +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    b +
    "," +
    a[11] +
    "(" +
    p +
    "))"
  let slot = lemma(
    "tlsf_malloc_cached_slot",
    page_quantify(model + [("p", w), ("b", w)]) +
    cond +
    " → (∃ i : Num, i < tlsf_small_total(" +
    a[9] +
    "(" +
    p +
    ")) && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    a[9] +
    "(" +
    p +
    "),i))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          part,
          seq([
            @tactics.undisch_tac(tm(block_backing(a))),
            rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
            small_meson(ths([])),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_malloc_cached_unique"), [
            p,
            a[9] + "(" + p + ")",
            a[10] + "(" + p + ")",
            a[11] + "(" + p + ")",
            a[12] + "(" + p + ")",
            b,
          ]),
        ),
        arw([thm("tlsf_small_slots_member")]),
        small_meson(ths([])),
      ])
    },
  )
  let geo = [3, 4, 8, 9, 10, 11, 12, 1, 13, 14].map(i => a[i])
  let pars = [
    a[1],
    p,
    "val(tlsf_size(" + a[4] + "(" + p + ")))",
    a[9] + "(" + p + ")",
    a[10] + "(" + p + ")",
    a[11] + "(" + p + ")",
    a[12] + "(" + p + ")",
  ]
  let bounds = lemma(
    "tlsf_malloc_cached_bounds",
    page_quantify(model + [("p", w), ("b", w)]) +
    cond +
    " → val(" +
    p +
    ")+32 <= val(" +
    b +
    ") && val(" +
    b +
    ")+8+" +
    a[9] +
    "(" +
    p +
    ") <= val(" +
    p +
    ")+8+val(tlsf_size(" +
    a[4] +
    "(" +
    p +
    "))) && !(" +
    b +
    " == word(0))",
    () => {
      seq([
        gen,
        strip,
        g => {
          @tactics.strip_assume_tac(block_under(inst(slot, a + [p, b]), g))(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_small_page_member_geometry"), geo + [p]),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.mp_tac(
            block_under(
              inst(thm("tlsf_small_slot_bounds"), pars + ["(i : Num)"]),
              g,
            ),
          )(g)
        },
        arw([]),
        small_meson(ths([])),
      ])
    },
  )
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let _ = lemma(
    "tlsf_malloc_cached_other",
    page_quantify(model + [("p", w), ("q", w), ("b", w)]) +
    physical +
    " && " +
    cond +
    " && MEM(" +
    q +
    "," +
    a[8] +
    ") && !(" +
    q +
    " == " +
    p +
    ") → !MEM(" +
    b +
    "," +
    a[11] +
    "(" +
    q +
    "))",
    () => {
      seq([
        gen,
        strip,
        @tactics.disch_tac,
        g => {
          @tactics.strip_assume_tac(block_under(inst(bounds, a + [p, b]), g))(g)
        },
        g => {
          @tactics.strip_assume_tac(block_under(inst(bounds, a + [q, b]), g))(g)
        },
        free_have(
          "tlsf_layout(word(0),tlsf_origin(" +
          a[0] +
          ")," +
          a[1] +
          "," +
          a[2] +
          "," +
          a[3] +
          "," +
          a[4] +
          ")",
          seq([
            @tactics.undisch_tac(tm(physical)),
            rw([thm("tlsf_physical_ok")]),
            small_meson(ths([])),
          ]),
        ),
        @tactics.mp_tac(
          inst(
            thm("tlsf_small_backing_separate"),
            [
              a[3],
              a[4],
              "(word(0) : " + w + ")",
              "tlsf_origin(" + a[0] + ")",
              a[1],
              a[2],
            ] +
            a[8:13].to_owned() +
            [p, q],
          ),
        ),
        arw([@theorems.eq_sym_eq()]),
        @int.asm_arith_tac,
      ])
    },
  )
}
