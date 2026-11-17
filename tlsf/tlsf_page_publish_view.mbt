// The page view leaves the three overwritten words and selected free link
// exposed. Slot headers, other live payload omissions and padding are shared.

///|
fn define_tlsf_page_publish_view() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let cell = (a : String, x : String) => {
    "pts(" + a + ",serialise_i32((" + x + " : " + w + ")))"
  }
  let own = small_star([
    cell("val((p : " + w + "))+8", "word((s : Num))"),
    cell("val((b : " + w + "))", "word(4)"),
    cell("val((b : " + w + "))+4", "p"),
    "tlsf_istar((j : Num) => if j == (i : Num) { emp } else { tlsf_small_slot_heap((p : " +
    w +
    "),(s : Num),(live : " +
    lw +
    "),j) },tlsf_small_total(s))",
    "tlsf_bytes(val((p : " +
    w +
    "))+32+(8+(s : Num))*tlsf_small_total(s),(cap : Num)-24-(8+s)*tlsf_small_total(s))",
  ])
  def(
    "tlsf_page_publish_frame",
    "tlsf_page_publish_frame((p : " +
    w +
    "),(cap : Num),(s : Num),(live : " +
    lw +
    "),(b : " +
    w +
    "),(i : Num)) == " +
    own,
  )
  def(
    "tlsf_page_publish_payload",
    "tlsf_page_publish_payload((b : " +
    w +
    "),(s : Num)) == star(" +
    cell("val(b)+8", "word(0)") +
    ",tlsf_bytes(val(b)+12,s-4))",
  )
}

///|
fn prove_tlsf_page_publish_view() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let vs = "∀ lim : Num, ∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, ∀ b : " +
    w +
    ", ∀ bs : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ i : Num"
  let ok = "tlsf_small_page_ok((lim : Num),(p : " +
    w +
    "),(cap : Num),(s : Num),CONS((b : " +
    w +
    "),(bs : " +
    lw +
    ")),NIL,(live : " +
    lw +
    ")) && (i : Num) < tlsf_small_total(s) && b == tlsf_small_slot(p,s,i)"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let cell = (off : Int32, x : String) => {
    "pts(val((p : " +
    w +
    "))+" +
    off.to_string() +
    ",serialise_i32((" +
    x +
    " : " +
    w +
    ")))"
  }
  let frame = "tlsf_page_publish_frame((p : " +
    w +
    "),(cap : Num),(s : Num),(live : " +
    lw +
    "),(b : " +
    w +
    "),(i : Num))"
  let body = (u : String, head : String) => {
    small_star([
      cell(12, "word(tlsf_small_total((s : Num)))"),
      cell(16, u),
      cell(20, head),
      frame,
      "tlsf_small_links((bs : " + lw + "))",
      "tlsf_bytes(val((b : " + w + "))+12,(s : Num)-4)",
    ])
  }
  let old = "tlsf_small_page_heap((p : " +
    w +
    "),(cap : Num),(s : Num),CONS((b : " +
    w +
    "),(bs : " +
    lw +
    ")),NIL,(live : " +
    lw +
    "))"
  let newer = "tlsf_small_page_heap((p : " +
    w +
    "),(cap : Num),(s : Num),NIL,(bs : " +
    lw +
    "),CONS((b : " +
    w +
    "),(live : " +
    lw +
    ")))"
  let prepare = seq([
    gen,
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    free_have(
      "tlsf_small_partition((p : " +
      w +
      "),(s : Num),CONS((b : " +
      w +
      "),(bs : " +
      lw +
      ")),NIL,(live : " +
      lw +
      "))",
      seq([
        @tactics.undisch_tac(tm(show(@basics.dest_conj(tm(ok)).0))),
        rw([thm("tlsf_small_page_ok")]),
        small_meson(ths([])),
      ]),
    ),
    free_have(
      "!MEM((b : " + w + "),(live : " + lw + "))",
      seq([
        @tactics.mp_tac(
          inst(thm("tlsf_page_publish_local_unique"), [
            "(p : " + w + ")",
            "(s : Num)",
            "CONS((b : " + w + "),(bs : " + lw + "))",
            "(NIL : " + lw + ")",
            "(live : " + lw + ")",
            "(b : " + w + ")",
          ]),
        ),
        arw([@lists.mem()]),
        small_meson(ths([])),
      ]),
    ),
    free_have(
      "tlsf_small_used((NIL : " +
      lw +
      "),(live : " +
      lw +
      ")) < tlsf_small_total((s : Num))",
      seq([
        @tactics.undisch_tac(
          tm(
            "tlsf_small_partition((p : " +
            w +
            "),(s : Num),CONS((b : " +
            w +
            "),(bs : " +
            lw +
            ")),NIL,(live : " +
            lw +
            "))",
          ),
        ),
        rw([thm("tlsf_small_partition"), @lists.length()]),
        @tactics.strip_tac,
        @int.asm_arith_tac,
      ]),
    ),
    free_have(
      "∀ j : Num, j < tlsf_small_total((s : Num)) && !(j == (i : Num)) → !(tlsf_small_slot((p : " +
      w +
      "),s,j) == (b : " +
      w +
      "))",
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.mp_tac(
          inst(thm("tlsf_small_slot_injective"), [
            "(lim : Num)",
            "(p : " + w + ")",
            "(cap : Num)",
            "(s : Num)",
            "CONS((b : " + w + "),(bs : " + lw + "))",
            "(NIL : " + lw + ")",
            "(live : " + lw + ")",
            "(j : Num)",
            "(i : Num)",
          ]),
        ),
        arw([]),
        small_meson(ths([])),
      ]),
    ),
  ])
  let pars = [
    "tlsf_small_total((s : Num))",
    "(p : " + w + ")",
    "(s : Num)",
    "(live : " + lw + ")",
    "(b : " + w + ")",
    "(i : Num)",
  ]
  let _ = lemma(
    "tlsf_page_publish_view_facts",
    vs +
    ", " +
    ok +
    " → !MEM(b,live) && (∀ j : Num, j < tlsf_small_total(s) && !(j == i) → !(tlsf_small_slot(p,s,j) == b))",
    () => seq([prepare, arw([])]),
  )
  let _ = lemma(
    "tlsf_page_publish_page_pre",
    vs +
    ", " +
    ok +
    " → " +
    old +
    " == star(pts(val(b)+8,serialise_i32(tlsf_small_head(bs)))," +
    body("word(tlsf_small_used((NIL : " + lw + "),(live : " + lw + ")))", "b") +
    ")",
    () => {
      seq([
        prepare,
        g => {
          @tactics.assume_tac(
            block_under(inst(thm("tlsf_page_publish_slots_pre"), pars), g),
          )(g)
        },
        rw([
          thm("tlsf_small_page_heap"),
          thm("tlsf_page_publish_frame"),
          thm("tlsf_small_links"),
          thm("tlsf_small_head"),
          @lists.not_cons_nil(),
          @lists.hd(),
        ]),
        arw(ac + [@arith.lt_refl()]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_page_publish_page_post",
    vs +
    ", " +
    ok +
    " → star(" +
    newer +
    ",star(tlsf_small_links(bs),tlsf_page_publish_payload(b,s))) == star(tlsf_bytes(val(p)+24,8),star(pts(val(b)+8,serialise_i32((word(0) : " +
    w +
    ")))," +
    body("word(tlsf_small_total((s : Num)))", "word(0)") +
    "))",
    () => {
      seq([
        prepare,
        g => {
          @tactics.assume_tac(
            block_under(inst(thm("tlsf_page_publish_slots_post"), pars), g),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_partition"), [
                "(p : " + w + ")",
                "(s : Num)",
                "(b : " + w + ")",
                "(bs : " + lw + ")",
                "(live : " + lw + ")",
              ]),
              g,
            ),
          )(g)
        },
        rw([
          thm("tlsf_small_page_heap"),
          thm("tlsf_page_publish_frame"),
          thm("tlsf_page_publish_payload"),
          thm("tlsf_small_links"),
          thm("tlsf_small_head"),
          @arith.lt_refl(),
        ]),
        arw(ac + [@arith.lt_refl()]),
      ])
    },
  )
}
