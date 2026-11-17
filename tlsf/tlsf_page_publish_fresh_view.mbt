// Bridge the precise unpublished-page result of compiled Page::allocate to
// the same slot-ownership view used for an existing partial page.

///|
fn prove_tlsf_page_publish_fresh_view() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let cell = (a : String, x : String) => {
    "pts(" + a + ",serialise_i32((" + x + " : " + w + ")))"
  }
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let s = "(s : Num)"
  let bs = "(bs : " + lw + ")"
  let total = "tlsf_small_total(" + s + ")"
  let old = "tlsf_page_allocate_build(" +
    p +
    ",(cap : Num)," +
    s +
    "," +
    total +
    ",(used0 : " +
    w +
    "),(prev0 : " +
    w +
    "))"
  let fields = small_star([
    cell("val(" + p + ")+12", "word(" + total + ")"),
    cell("val(" + p + ")+16", "used0"),
    cell("val(" + p + ")+20", b),
    cell("val(" + p + ")+24", "prev0"),
    cell("val(" + p + ")+28", "word(0)"),
    cell("val(" + b + ")+8", "tlsf_small_head(" + bs + ")"),
    "tlsf_page_publish_frame(" +
    p +
    ",(cap : Num)," +
    s +
    ",(NIL : " +
    lw +
    ")," +
    b +
    ",(i : Num))",
    "tlsf_small_links(" + bs + ")",
    "tlsf_bytes(val(" + b + ")+12," + s + "-4)",
  ])
  let ok = "tlsf_small_page_ok((lim : Num)," +
    p +
    ",(cap : Num)," +
    s +
    ",CONS(" +
    b +
    "," +
    bs +
    "),NIL,NIL) && (i : Num) < " +
    total +
    " && b == tlsf_small_slot(p,s,i) && REVERSE(tlsf_small_slots(p,s," +
    total +
    ")) == CONS(b,bs)"
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_page_publish_fresh_view",
    "∀ lim : Num, ∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, ∀ b : " +
    w +
    ", ∀ bs : " +
    lw +
    ", ∀ i : Num, ∀ used0 : " +
    w +
    ", ∀ prev0 : " +
    w +
    ", " +
    ok +
    " → " +
    old +
    " == " +
    fields,
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_view_facts"), [
                "(lim : Num)",
                p,
                "(cap : Num)",
                s,
                b,
                bs,
                "(NIL : " + lw + ")",
                "(i : Num)",
              ]),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_slots_pre"), [
                total,
                p,
                s,
                "(NIL : " + lw + ")",
                b,
                "(i : Num)",
              ]),
              g,
            ),
          )(g)
        },
        rw([
          thm("tlsf_page_allocate_build"),
          thm("tlsf_page_allocate_slots_refine"),
          @equal.gsym(thm("tlsf_page_allocate_list_head")),
          thm("tlsf_page_publish_frame"),
        ]),
        arw(
          [
            thm("tlsf_small_links"),
            thm("tlsf_small_head"),
            @lists.not_cons_nil(),
            @lists.hd(),
          ] +
          ac,
        ),
      ])
    },
  )
  let split4 = red(
    inst(thm("tlsf_bytes_split"), ["val((b : " + w + "))+8", "4", "(s : Num)-4"]),
  )
  let _ = lemma(
    "tlsf_page_publish_payload_bytes",
    "∀ b : " +
    w +
    ", ∀ s : Num, ∀ h : " +
    heap +
    ", 4 <= s && tlsf_page_publish_payload(b,s,h) → tlsf_bytes(val(b)+8,s,h)",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have("4+((s : Num)-4) == s", @int.asm_arith_tac),
        g => {
          let eq = @simp.rewrite_rule(g.0.map(p => p.1))(split4)
          seq([
            @tactics.subst1_tac(eq),
            @tactics.undisch_tac(
              tm(
                "tlsf_page_publish_payload((b : " +
                w +
                "),(s : Num),(h : " +
                heap +
                "))",
              ),
            ),
            ent_tac(
              [
                thm("tlsf_page_publish_payload"),
                thm("tlsf_bytes_word"),
                arith("∀ a : Num, (a+8)+4 == a+12"),
              ],
              ["(word(0) : " + w + ")"],
            ),
          ])(g)
        },
      ])
    },
  )
  let split8 = red(inst(thm("tlsf_bytes_split"), ["(a : Num)", "4", "4"]))
  let _ = lemma(
    "tlsf_page_publish_two_words",
    "∀ a : Num, ∀ v : " +
    w +
    ", ∀ u : " +
    w +
    ", ∀ h : " +
    heap +
    ", star(" +
    cell("(a : Num)", "v") +
    "," +
    cell("a+4", "u") +
    ",h) → tlsf_bytes(a,8,h)",
    () => {
      ent_tac([split8, thm("tlsf_bytes_word")], [
        "(v : " + w + ")",
        "(u : " + w + ")",
      ])
    },
  )
}
