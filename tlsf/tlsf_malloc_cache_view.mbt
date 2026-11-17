// Removing a cached block leaves Page.used unchanged. The newly live slot's
// spare bytes are transferred out of page ownership; all other slots agree.

///|
fn prove_tlsf_malloc_cache_view() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let vs = [
    ("lim", "Num"),
    ("p", w),
    ("cap", "Num"),
    ("s", "Num"),
    ("loc", lw),
    ("cached", lw),
    ("live", lw),
    ("b", w),
    ("i", "Num"),
  ]
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let s = "(s : Num)"
  let c = "(cached : " + lw + ")"
  let l = "(live : " + lw + ")"
  let loc = "(loc : " + lw + ")"
  let nc = "tlsf_small_remove(" + b + "," + c + ")"
  let ready = "tlsf_small_page_ok((lim : Num)," +
    p +
    ",(cap : Num)," +
    s +
    "," +
    loc +
    "," +
    c +
    "," +
    l +
    ")"
  let cond = ready +
    " && MEM(" +
    b +
    "," +
    c +
    ") && (i : Num) < tlsf_small_total(s) && b == tlsf_small_slot(p,s,i)"
  let old = "tlsf_small_page_heap(" +
    p +
    ",(cap : Num)," +
    s +
    "," +
    loc +
    "," +
    c +
    "," +
    l +
    ")"
  let newer = "tlsf_small_page_heap(" +
    p +
    ",(cap : Num)," +
    s +
    "," +
    loc +
    "," +
    nc +
    ",CONS(" +
    b +
    "," +
    l +
    "))"
  let args = ["(lim : Num)", p, "(cap : Num)", s, loc, c, l]
  let slotargs = ["tlsf_small_total(" + s + ")", p, s, l, b, "(i : Num)"]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_cache_page_view",
    page_quantify(vs) +
    cond +
    " → " +
    old +
    " == star(tlsf_bytes(val(" +
    b +
    ")+12," +
    s +
    "-4)," +
    newer +
    ")",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "tlsf_small_partition(" +
          p +
          "," +
          s +
          "," +
          loc +
          "," +
          c +
          "," +
          l +
          ")",
          seq([
            @tactics.undisch_tac(tm(ready)),
            rw([thm("tlsf_small_page_ok")]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_malloc_cached_partition"), [p, s, loc, c, l, b]),
              g,
            ),
          )(g)
        },
        free_have(
          "∀ j : Num, j < tlsf_small_total(" +
          s +
          ") && !(j == (i : Num)) → !(tlsf_small_slot(" +
          p +
          "," +
          s +
          ",j) == " +
          b +
          ")",
          seq([
            gen,
            strip,
            @tactics.mp_tac(
              inst(
                thm("tlsf_small_slot_injective"),
                args + ["(j : Num)", "(i : Num)"],
              ),
            ),
            arw([]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          let pre = block_under(
            inst(thm("tlsf_page_publish_slots_pre"), slotargs),
            g,
          )
          let post = block_under(
            inst(thm("tlsf_page_publish_slots_post"), slotargs),
            g,
          )
          seq([rw([thm("tlsf_small_page_heap"), pre, post]), arw(malloc_ac())])(
            g,
          )
        },
      ])
    },
  )
}
