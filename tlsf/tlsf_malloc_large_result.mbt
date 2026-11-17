///|
fn prove_tlsf_malloc_large_result() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let m = "(m : " + w + ")"
  let n = "(n : " + w + ")"
  let oldlim = "(oldlim : Num)"
  let fp = "(fp : " + rty + ")"
  let gs = "(gs : List[Value])"
  let h = "(h : " + heap + ")"
  let cap = "val(tlsf_size(" + a[4] + "(" + m + ")))"
  let ptr = "word_add(" + m + ",word(8))"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let client = "star(tlsf_allocator(" +
    a.join(",") +
    "),(" +
    fp +
    ")(" +
    gs +
    "," +
    oldlim +
    "))"
  let spatial = "star(tlsf_bytes(val(" +
    m +
    ")+8," +
    cap +
    ")," +
    client +
    "," +
    h +
    ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vs = page_model_variables() +
    [
      ("m", w),
      ("n", w),
      ("oldlim", "Num"),
      ("fp", rty),
      ("gs", "List[Value]"),
      ("h", heap),
    ]
  let _ = lemma(
    "tlsf_malloc_large_result",
    page_quantify(vs) +
    physical +
    " && MEM(" +
    m +
    "," +
    a[3] +
    ") && !MEM(" +
    m +
    "," +
    a[8] +
    ") && tlsf_used(" +
    a[4] +
    "(" +
    m +
    ")) && val(" +
    n +
    ") <= " +
    cap +
    " && " +
    oldlim +
    " <= " +
    a[1] +
    " && " +
    spatial +
    " → tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    oldlim +
    "," +
    fp +
    "," +
    ptr +
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
          ") && " +
          a[1] +
          " <= 4294967296",
          seq([
            @tactics.undisch_tac(tm(physical)),
            rw([thm("tlsf_physical_ok")]),
            page_publish_atomic([]),
          ]),
        ),
        split_conjs(),
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_layout_members"), [
                a[3],
                "(word(0) : " + w + ")",
                "tlsf_origin(" + a[0] + ")",
                a[1],
                a[2],
                a[4],
                m,
              ]),
              g,
            ),
          )(g)
        },
        free_have(
          "val(" + m + ")+8+" + cap + " <= " + a[1] + " && 16 <= " + cap,
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_block_ok(val(" +
                m +
                ")," +
                a[1] +
                "," +
                m +
                "," +
                a[4] +
                ")",
              ),
            ),
            rw([thm("tlsf_block_ok")]),
            page_publish_atomic([]),
          ]),
        ),
        split_conjs(),
        free_have(
          "val(" + ptr + ") == val(" + m + ")+8",
          seq([@logic.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        ),
        free_have(
          "!(" + ptr + " == word(0)) && !(" + ptr + " == word(4294967295))",
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
        rw([thm("tlsf_malloc_result")]),
        beta_goal(),
        seq(
          page_model_variables()[2:]
          .to_owned()
          .map(x => @tactics.exists_tac(tm("(" + x.0 + " : " + x.1 + ")"))),
        ),
        @tactics.exists_tac(tm(cap)),
        arw(malloc_ac()),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              seq([
                rw([thm("tlsf_malloc_owned")]),
                @tactics.disj1_tac,
                @tactics.exists_tac(tm(m)),
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
