///|
fn prove_tlsf_malloc_result() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let n = "(n : " + w + ")"
  let oldlim = "(oldlim : Num)"
  let fp = "(fp : " + rty + ")"
  let gs = "(gs : List[Value])"
  let h = "(h : " + heap + ")"
  let s = a[9] + "(" + p + ")"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let pb = "word_add(" + b + ",word(8))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let payload = "tlsf_page_publish_payload(" + b + "," + s + ")"
  let frame = "star(tlsf_allocator(" +
    a.join(",") +
    "),(" +
    fp +
    ")(" +
    gs +
    "," +
    oldlim +
    "))"
  let vs = model +
    [
      ("p", w),
      ("b", w),
      ("n", w),
      ("oldlim", "Num"),
      ("fp", rty),
      ("gs", "List[Value]"),
      ("h", heap),
    ]
  let _ = lemma(
    "tlsf_malloc_payload_frame",
    "∀ b : " +
    w +
    ", ∀ sz : Num, ∀ frame : " +
    hprop +
    ", ∀ h : " +
    heap +
    ", 4 <= sz && star(tlsf_page_publish_payload(b,sz),frame,h) → star(tlsf_bytes(val(b)+8,sz),frame,h)",
    () => {
      seq([
        gen,
        rw([thm("star")]),
        strip,
        @tactics.exists_tac(tm("(h1 : " + heap + ")")),
        @tactics.exists_tac(tm("(h2 : " + heap + ")")),
        arw([]),
        @logic.match_mp_tac(thm("tlsf_page_publish_payload_bytes")),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_malloc_small_result",
    page_quantify(vs) +
    physical +
    " && " +
    block_backing(a) +
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
    ")) && " +
    oldlim +
    " <= " +
    a[1] +
    " && val(" +
    n +
    ") <= " +
    s +
    " && star(" +
    payload +
    "," +
    frame +
    "," +
    h +
    ") → tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    oldlim +
    "," +
    fp +
    "," +
    pb +
    ")(" +
    gs +
    "," +
    a[1] +
    "," +
    h +
    ")",
    () => {
      seq([
        gen,
        strip,
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_live_slot"), a + [p, b]), g),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_small_page_member_geometry"), [
                a[3],
                a[4],
                a[8],
                a[9],
                a[10],
                a[11],
                a[12],
                a[1],
                a[13],
                a[14],
                p,
              ]),
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
                s,
                a[10] + "(" + p + ")",
                a[11] + "(" + p + ")",
                a[12] + "(" + p + ")",
                "(i : Num)",
              ]),
              g,
            ),
          )(g)
        },
        free_have(
          "val(" +
          b +
          ")+8+" +
          s +
          " <= " +
          a[1] +
          " && " +
          a[1] +
          " <= 4294967296 && 8 <= " +
          s,
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_small_page_ok(" +
                [
                  a[1],
                  p,
                  cap,
                  s,
                  a[10] + "(" + p + ")",
                  a[11] + "(" + p + ")",
                  a[12] + "(" + p + ")",
                ].join(",") +
                ")",
              ),
            ),
            rw([thm("tlsf_small_page_ok")]),
            strip,
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        split_conjs(),
        free_have(
          "val(" + pb + ") == val(" + b + ")+8",
          seq([@logic.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        g => {
          let eq = @kernel.assume_rule(
            tm(b + " == tlsf_small_slot(" + p + "," + s + ",(i : Num))"),
          )
          @tactics.rule_assum_tac(th => {
            if @kernel.concl(th) == @kernel.concl(eq) {
              th
            } else {
              @simp.rewrite_rule(ths([eq]))(th)
            }
          })(g)
        },
        free_have(
          "!(" + pb + " == word(0)) && !(" + pb + " == word(4294967295))",
          seq([
            rw([
              @equal.gsym(@words.val_eq()),
              @words.val_word(),
              @words.dimindex_32(),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        split_conjs(),
        free_have(
          "star(tlsf_bytes(val(" + pb + ")," + s + ")," + frame + "," + h + ")",
          seq([
            arw([]),
            g => {
              free_apply(
                @simp.rewrite_rule(g.0.map(x => x.1))(
                  inst(thm("tlsf_malloc_payload_frame"), [b, s, frame, h]),
                ),
              )(g)
            },
            @tactics.try_tac(@int.asm_arith_tac),
          ]),
        ),
        g => {
          let eq = @kernel.assume_rule(
            tm(b + " == tlsf_small_slot(" + p + "," + s + ",(i : Num))"),
          )
          @tactics.rule_assum_tac(th => {
            if @kernel.concl(th) == @kernel.concl(eq) {
              th
            } else {
              @simp.rewrite_rule(ths([eq]))(th)
            }
          })(g)
        },
        rw([thm("tlsf_malloc_result")]),
        beta_goal(),
        seq(
          model[2:]
          .to_owned()
          .map(x => @tactics.exists_tac(tm("(" + x.0 + " : " + x.1 + ")"))),
        ),
        @tactics.exists_tac(tm(s)),
        arw(malloc_ac()),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              seq([
                rw([thm("tlsf_malloc_owned")]),
                @tactics.disj2_tac,
                @tactics.exists_tac(tm(p)),
                @tactics.exists_tac(tm(b)),
                arw([]),
              ]),
            ),
            solve(
              @tactics.first_assum(th => {
                if head_name(@kernel.concl(th)) == "star" {
                  seq([
                    @tactics.undisch_tac(@kernel.concl(th)),
                    arw(malloc_ac()),
                  ])
                } else {
                  @tactics.no_tac
                }
              }),
            ),
            solve(@int.asm_arith_tac),
          ]),
        ),
      ])
    },
  )
}
