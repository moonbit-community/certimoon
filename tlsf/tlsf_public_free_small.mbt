// Live small slots retain their allocator-owned tag and page-pointer words.

///|
fn prove_tlsf_public_free_small() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
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
  let slot = "tlsf_small_slot(" + p + ",(s : Num),(i : Num))"
  let vars = "∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, ∀ loc : " +
    lw +
    ", ∀ cached : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", ∀ i : Num"
  let page = "tlsf_small_page_heap(" +
    p +
    ",(cap : Num),(s : Num),(loc : " +
    lw +
    "),(cached : " +
    lw +
    "),(live : " +
    lw +
    "))"
  let _ = lemma(
    "tlsf_public_free_slot_view",
    vars +
    ", i < tlsf_small_total(s) && b == " +
    slot +
    " && MEM(b,live) → (∃ rest : " +
    hprop +
    ", " +
    page +
    " == star(pts(val(b),serialise_i32((word(4) : " +
    w +
    "))),rest))",
    () => {
      seq([
        gen,
        strip,
        subst_only("b"),
        @tactics.mp_tac(
          inst(thm("tlsf_small_page_slot_focus"), [
            p,
            "(cap : Num)",
            "(s : Num)",
            "(loc : " + lw + ")",
            "(cached : " + lw + ")",
            "(live : " + lw + ")",
            "(i : Num)",
          ]),
        ),
        arw([]),
        strip,
        @tactics.exists_tac(
          tm(
            "star(pts(val(" +
            slot +
            ")+4,serialise_i32(" +
            p +
            ")),(rest : " +
            hprop +
            "))",
          ),
        ),
        arw([thm("tlsf_small_slot_heap")] + ac),
      ])
    },
  )
  let conditions = block_backing(a) +
    " && " +
    block_lists(a) +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    b +
    "," +
    a[12] +
    "(" +
    p +
    "))"
  let i = "(i : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let pg = "tlsf_small_page_ok(" +
    [
      a[1],
      p,
      cap,
      a[9] + "(" + p + ")",
      a[10] + "(" + p + ")",
      a[11] + "(" + p + ")",
      a[12] + "(" + p + ")",
    ].join(",") +
    ")"
  let geometry = [3, 4, 8, 9, 10, 11, 12, 1, 13, 14].map(k => a[k]) + [p]
  let _ = lemma(
    "tlsf_public_free_small_geometry",
    page_quantify(page_model_variables() + [("p", w), ("b", w)]) +
    "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    conditions +
    " → val(word_add(" +
    b +
    ",word(8))) == val(" +
    b +
    ")+8 && !word_ult(word_add(" +
    b +
    ",word(8)),word_add(tlsf_base(" +
    a[0] +
    "),word(2184)))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "MEM(" + p + "," + a[3] + ")",
          seq([
            @tactics.undisch_tac(tm(block_backing(a))),
            rw([thm("tlsf_small_backing")]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_public_free_block_geometry"), a + [p]),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_live_slot"), a + [p, b]), g),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_small_page_member_geometry"), geometry),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_small_slot_bounds"), [
                a[1],
                p,
                cap,
                a[9] + "(" + p + ")",
                a[10] + "(" + p + ")",
                a[11] + "(" + p + ")",
                a[12] + "(" + p + ")",
                i,
              ]),
              g,
            ),
          )(g)
        },
        @logic.match_mp_tac(thm("tlsf_public_free_pointer_guard")),
        @tactics.undisch_tac(tm(pg)),
        rw([thm("tlsf_small_page_ok")]),
        strip,
        free_have(
          "tlsf_origin(" + a[0] + ") <= val(" + b + ")",
          seq([arw([]), @int.asm_arith_tac]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_public_free_read_small",
    page_quantify(
      page_model_variables() +
      [("p", w), ("b", w), ("client", hprop), ("h", heap)],
    ) +
    conditions +
    " → (star(tlsf_allocator(" +
    a.join(",") +
    "),(client : " +
    hprop +
    "),(h : " +
    heap +
    ")) → has_i32(h,val(" +
    b +
    "),(word(4) : " +
    w +
    ")))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "tlsf_count(" + p + "," + a[8] + ") == 1",
          seq([
            @tactics.undisch_tac(tm(block_lists(a))),
            rw([thm("tlsf_small_lists_ok")]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_live_slot"), a + [p, b]), g),
          )(g)
        },
        @tactics.mp_tac(
          inst(thm("tlsf_public_free_slot_view"), [
            p,
            cap,
            a[9] + "(" + p + ")",
            a[10] + "(" + p + ")",
            a[11] + "(" + p + ")",
            a[12] + "(" + p + ")",
            b,
            i,
          ]),
        ),
        arw([]),
        strip,
        g => {
          let focus = block_under(
            inst(thm("tlsf_small_pages_focus"), [
              a[8],
              a[4],
              a[9],
              a[10],
              a[11],
              a[12],
              p,
            ]),
            g,
          )
          let view = g.0
            .to_array()
            .map(x => x.1)
            .filter(th => {
              if args_of(@kernel.concl(th), "=", 2) is Some([lhs, _]) {
                head_name(lhs) == "tlsf_small_page_heap"
              } else {
                false
              }
            })
          public_free_read_tac(
            [thm("tlsf_allocator"), thm("tlsf_small"), focus] + view,
          )(g)
        },
      ])
    },
  )
}
