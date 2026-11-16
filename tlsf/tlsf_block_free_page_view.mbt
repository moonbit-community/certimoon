// A page release exposes exactly four mutable words. The remaining slots,
// spare bytes, and complete caller frame are shared by the two heap views.

///|
fn define_tlsf_block_free_page_view() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let gate = "if tlsf_small_used((cached : \{lw}),(live : \{lw})) < tlsf_small_total((s : Num)) { emp } else { tlsf_bytes(val((p : \{w}))+24,8) }"
  let own = small_star([
    cell("val((p : " + w + "))+8", "word((s : Num))"),
    cell("val((p : " + w + "))+12", "word(tlsf_small_total((s : Num)))"),
    cell("val((b : " + w + "))", "word(4)"),
    gate,
    "tlsf_istar((j : Num) => if j == (i : Num) { emp } else { tlsf_small_slot_heap((p : \{w}),(s : Num),(live : \{lw}),j) },tlsf_small_total(s))",
    "tlsf_small_links((loc : \{lw}))",
    "tlsf_bytes(val((b : \{w}))+12,(s : Num)-4)",
    "tlsf_bytes(val((p : \{w}))+32+(8+(s : Num))*tlsf_small_total(s),(cap : Num)-24-(8+s)*tlsf_small_total(s))",
  ])
  def(
    "tlsf_block_free_release_frame",
    "tlsf_block_free_release_frame((p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}),(b : \{w}),(i : Num)) == \{own}",
  )
}

///|
fn prove_tlsf_block_free_page_view() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
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
  let args = [
    "(p : " + w + ")",
    "(cap : Num)",
    "(s : Num)",
    "(loc : " + lw + ")",
    "(cached : " + lw + ")",
    "(live : " + lw + ")",
    "(b : " + w + ")",
    "(i : Num)",
  ]
  let frame = "tlsf_block_free_release_frame(" + args.join(",") + ")"
  let v = "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ b : \{w}, ∀ i : Num"
  let ok = "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) && (i : Num) < tlsf_small_total(s) && (b : \{w}) == tlsf_small_slot(p,s,i) && MEM(b,live)"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let cells = (u : String, h : String, nx : String) => {
    small_star([
      cell("val((b : " + w + "))+4", "p"),
      cell("val((b : " + w + "))+8", nx),
      cell("val((p : " + w + "))+16", u),
      cell("val((p : " + w + "))+20", h),
      frame,
    ])
  }
  let old = "tlsf_small_page_heap((p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let newlive = "tlsf_small_remove((b : \{w}),(live : \{lw}))"
  let un = "tlsf_small_used((cached : \{lw}),\{newlive})"
  let newer = "tlsf_small_page_heap((p : \{w}),(cap : Num),(s : Num),CONS((b : \{w}),(loc : \{lw})),(cached : \{lw}),\{newlive})"
  let gate = "if tlsf_small_used((cached : \{lw}),(live : \{lw})) < tlsf_small_total((s : Num)) { emp } else { tlsf_bytes(val((p : \{w}))+24,8) }"
  let expose = seq([
    gen,
    strip,
    free_have(
      "8 <= (s : Num)",
      seq([
        @tactics.undisch_tac(
          tm(
            "tlsf_small_page_ok((lim : " +
            "Num" +
            "),(p : " +
            w +
            "),(cap : Num),(s : Num),(loc : " +
            lw +
            "),(cached : " +
            lw +
            "),(live : " +
            lw +
            "))",
          ),
        ),
        rw([thm("tlsf_small_page_ok")]),
        small_meson(ths([])),
      ]),
    ),
    free_have("4 <= (s : Num)", @int.asm_arith_tac),
    free_have(
      "MEM(tlsf_small_slot((p : \{w}),(s : Num),(i : Num)),(live : \{lw}))",
      small_meson(ths([])),
    ),
  ])
  let _ = lemma(
    "tlsf_small_page_release_pre_view",
    "\{v}, \{ok} → star(\{old},tlsf_bytes(val(b)+8,s)) == ((h : \{heap}) => ∃ oldword : \{w}, \{cells("word(tlsf_small_used((cached : "+lw+"),(live : "+lw+")))","tlsf_small_head((loc : "+lw+"))","oldword")}(h))",
    seq([
      expose,
      free_have(
        "tlsf_small_slot_heap((p : \{w}),(s : Num),(live : \{lw}),(i : Num)) == star(pts(val(tlsf_small_slot(p,s,i)),serialise_i32((word(4) : \{w}))),pts(val(tlsf_small_slot(p,s,i))+4,serialise_i32(p)))",
        seq([@tactics.match_mp_tac(thm("tlsf_small_live_owned")), arw([])]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_istar_focus"), [
          "tlsf_small_total((s : Num))",
          "tlsf_small_slot_heap((p : " + w + "),(s : Num),(live : " + lw + "))",
          "(i : Num)",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_page_allocate_word_prefix"), [
          "val((b : " + w + "))+8",
          "(s : Num)",
        ]),
      ),
      arw([]),
      strip,
      rw([thm("tlsf_small_page_heap"), thm("tlsf_block_free_release_frame")]),
      arw(
        [thm("tlsf_small_live_owned"), arith("∀ a : Num, (a+8)+4 == a+12")] +
        ac +
        lift_rws(),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_small_page_release_post_view",
    "\{v}, \{ok} → \{cells("word("+un+")","b","tlsf_small_head((loc : "+lw+"))")} == star(\{newer},\{gate})",
    seq([
      expose,
      free_have(
        "∀ j : Num, j < tlsf_small_total((s : Num)) && !(j == (i : Num)) → !(tlsf_small_slot((p : \{w}),s,j) == (b : \{w}))",
        seq([
          gen,
          strip,
          @tactics.mp_tac(
            inst(thm("tlsf_small_slot_injective"), [
              "(lim : Num)",
              "(p : " + w + ")",
              "(cap : Num)",
              "(s : Num)",
              "(loc : " + lw + ")",
              "(cached : " + lw + ")",
              "(live : " + lw + ")",
              "(j : Num)",
              "(i : Num)",
            ]),
          ),
          arw([]),
          small_meson(ths([])),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_release_slots_focus"), [
          "tlsf_small_total((s : Num))",
          "(p : " + w + ")",
          "(s : Num)",
          "(live : " + lw + ")",
          "(b : " + w + ")",
          "(i : Num)",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      free_have(
        "tlsf_small_partition((p : \{w}),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))",
        seq([
          @tactics.undisch_tac(
            tm(
              "tlsf_small_page_ok((lim : Num),(p : " +
              w +
              "),(cap : Num),(s : Num),(loc : " +
              lw +
              "),(cached : " +
              lw +
              "),(live : " +
              lw +
              "))",
            ),
          ),
          rw([thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      free_have(
        "\{un} < tlsf_small_total((s : Num))",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_small_release_model"), [
              "(p : " + w + ")",
              "(s : Num)",
              "(b : " + w + ")",
              "(loc : " + lw + ")",
              "(cached : " + lw + ")",
              "(live : " + lw + ")",
            ]),
          ),
          arw([]),
          strip,
          @tactics.mp_tac(
            inst(thm("tlsf_small_accounting"), [
              "(p : " + w + ")",
              "(s : Num)",
              "(loc : " + lw + ")",
              "(cached : " + lw + ")",
              "(live : " + lw + ")",
            ]),
          ),
          arw([]),
          strip,
          @int.asm_arith_tac,
        ]),
      ),
      rw([thm("tlsf_small_page_heap"), thm("tlsf_block_free_release_frame")]),
      rw([
        @kernel.assume_rule(
          tm(
            "(b : " +
            w +
            ") == tlsf_small_slot((p : " +
            w +
            "),(s : Num),(i : Num))",
          ),
        ),
      ]),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([
            @kernel.assume_rule(
              tm(
                "(b : " +
                w +
                ") == tlsf_small_slot((p : " +
                w +
                "),(s : Num),(i : Num))",
              ),
            ),
          ]),
        ),
      ),
      arw(
        [
          thm("tlsf_small_slot_heap"),
          thm("tlsf_small_remove_member"),
          thm("tlsf_small_links"),
          thm("tlsf_small_head"),
          @lists.not_cons_nil(),
          @lists.hd(),
        ] +
        ac,
      ),
    ]),
  )
}
