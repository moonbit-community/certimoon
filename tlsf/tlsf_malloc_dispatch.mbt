// Dispatch choices follow from the global lists and page partitions.

///|
fn prove_tlsf_malloc_cached_dispatch() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let page = "tlsf_small_page_ok(" +
    [
      a[1],
      p,
      cap,
      "8*" + k,
      a[10] + "(" + p + ")",
      a[11] + "(" + p + ")",
      a[12] + "(" + p + ")",
    ].join(",") +
    ")"
  let need = page +
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
    ")) && " +
    a[9] +
    "(" +
    p +
    ") == 8*" +
    k +
    " && tlsf_count(" +
    p +
    "," +
    a[8] +
    ") == 1 && (i : Num) < tlsf_small_total(8*" +
    k +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    ",8*" +
    k +
    ",i)"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_cached_dispatch",
    page_quantify(page_model_variables() + [("k", "Num"), ("b", w), ("bs", lw)]) +
    block_backing(a) +
    " && " +
    block_lists(a) +
    " && " +
    k +
    " < 33 && " +
    a[13] +
    "(" +
    k +
    ") == CONS(" +
    b +
    "," +
    bs +
    ") → (∃ p : " +
    w +
    ", ∃ i : Num, " +
    need +
    ")",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "∃ p : " +
          w +
          ", MEM(p," +
          a[8] +
          ") && " +
          a[9] +
          "(p) == 8*" +
          k +
          " && MEM(" +
          b +
          "," +
          a[11] +
          "(p))",
          seq([
            @tactics.undisch_tac(tm(block_lists(a))),
            rw([thm("tlsf_small_lists_ok")]),
            strip,
            @tactics.first_assum(th => @logic.match_mp_tac(th)),
            arw([@lists.mem()]),
          ]),
        ),
        @tactics.first_x_assum(th => {
          if @basics.is_exists(@kernel.concl(th)) {
            @tactics.x_choose_then(tm(p))(th => @tactics.strip_assume_tac(th))(
              th,
            )
          } else {
            @tactics.no_tac
          }
        }),
        g => {
          @tactics.strip_assume_tac(
            @simp.rewrite_rule(g.0.map(x => x.1))(
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
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            @simp.rewrite_rule(g.0.map(x => x.1))(
              block_under(inst(thm("tlsf_malloc_cached_slot"), a + [p, b]), g),
            ),
          )(g)
        },
        free_have(
          "tlsf_count(" + p + "," + a[8] + ") == 1",
          seq([
            @tactics.undisch_tac(tm(block_lists(a))),
            rw([thm("tlsf_small_lists_ok")]),
            strip,
            page_publish_old_page_facts(p),
            arw([]),
          ]),
        ),
        @tactics.exists_tac(tm(p)),
        @tactics.exists_tac(tm("(i : Num)")),
        arw([]),
      ])
    },
  )
}

///|
fn prove_tlsf_malloc_partial_dispatch() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let z = "(z : " + lw + ")"
  let k = "(k : Num)"
  let s = "8*" + k
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let page = "tlsf_small_page_ok(" +
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
  let used = "tlsf_small_used(" +
    a[11] +
    "(" +
    p +
    ")," +
    a[12] +
    "(" +
    p +
    "))"
  let facts = "MEM(" +
    p +
    "," +
    a[8] +
    ") && " +
    a[9] +
    "(" +
    p +
    ") == " +
    s +
    " && 0 < " +
    used +
    " && " +
    used +
    " < tlsf_small_total(" +
    a[9] +
    "(" +
    p +
    "))"
  let ready = publish_ready(a, p, b, bs, s, a[12] + "(" + p + ")")
  let need = ready +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && " +
    a[9] +
    "(" +
    p +
    ") == " +
    s +
    " && " +
    a[10] +
    "(" +
    p +
    ") == CONS(" +
    b +
    "," +
    bs +
    ") && " +
    a[11] +
    "(" +
    p +
    ") == NIL && tlsf_count(" +
    p +
    "," +
    a[8] +
    ") == 1 && (i : Num) < tlsf_small_total(" +
    s +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    s +
    ",i) && (∀ q : " +
    w +
    ", MEM(q," +
    z +
    ") → !(q == word(0)) && val(q)+32 <= 4294967296)"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_partial_dispatch",
    page_quantify(page_model_variables() + [("k", "Num"), ("p", w), ("z", lw)]) +
    block_backing(a) +
    " && " +
    block_lists(a) +
    " && " +
    k +
    " < 33 && " +
    a[13] +
    "(" +
    k +
    ") == NIL && " +
    a[14] +
    "(" +
    k +
    ") == CONS(" +
    p +
    "," +
    z +
    ") → (∃ b : " +
    w +
    ", ∃ bs : " +
    lw +
    ", ∃ i : Num, " +
    need +
    ")",
    () => {
      seq([
        gen,
        strip,
        free_have(
          facts,
          seq([
            @tactics.undisch_tac(tm(block_lists(a))),
            rw([thm("tlsf_small_lists_ok")]),
            strip,
            @tactics.first_assum(th => @logic.match_mp_tac(th)),
            arw([@lists.mem()]),
          ]),
        ),
        split_conjs(),
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
        free_have(
          "DIV(" + a[9] + "(" + p + "),8) == " + k,
          seq([
            @logic.match_mp_tac(
              inst(@arith.div_uniq(), [a[9] + "(" + p + ")", "8", k, "0"]),
            ),
            @int.asm_arith_tac,
          ]),
        ),
        g => {
          @tactics.assume_tac(
            block_under(inst(thm("tlsf_page_publish_empty_cached"), a + [p]), g),
          )(g)
        },
        free_have(
          "!(" + a[10] + "(" + p + ") == NIL)",
          seq([
            @tactics.disch_tac,
            @tactics.undisch_tac(
              tm(used + " < tlsf_small_total(" + a[9] + "(" + p + "))"),
            ),
            @tactics.undisch_tac(tm(page)),
            rw([thm("tlsf_small_page_ok"), thm("tlsf_small_partition")]),
            arw([@lists.length()]),
            @tactics.repeat_tac(@tactics.strip_tac),
            @int.asm_arith_tac,
          ]),
        ),
        @tactics.mp_tac(
          @bool.ispec(tm(a[10] + "(" + p + ")"), @lists.list_cases()),
        ),
        @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
        @tactics.first(
          @list.List([
            solve(page_publish_atomic([])),
            solve(
              seq([
                @tactics.first_x_assum(th => {
                  if @basics.is_exists(@kernel.concl(th)) {
                    @tactics.x_choose_then(tm(b))(
                      @tactics.x_choose_then(tm(bs))(th => {
                        @tactics.assume_tac(th)
                      }),
                    )(th)
                  } else {
                    @tactics.no_tac
                  }
                }),
                free_have(ready, seq([@tactics.undisch_tac(tm(page)), arw([])])),
                g => {
                  @tactics.strip_assume_tac(
                    block_under(
                      inst(thm("tlsf_page_publish_local_index"), [
                        a[1],
                        p,
                        cap,
                        s,
                        b,
                        bs,
                        a[12] + "(" + p + ")",
                      ]),
                      g,
                    ),
                  )(g)
                },
                free_have(
                  "tlsf_count(" + p + "," + a[8] + ") == 1",
                  seq([
                    @tactics.undisch_tac(tm(block_lists(a))),
                    rw([thm("tlsf_small_lists_ok")]),
                    strip,
                    page_publish_old_page_facts(p),
                    arw([]),
                  ]),
                ),
                @tactics.exists_tac(tm(b)),
                @tactics.exists_tac(tm(bs)),
                @tactics.exists_tac(tm("(i : Num)")),
                arw([]),
                g => {
                  @tactics.assume_tac(
                    block_under(
                      inst(thm("tlsf_small_partial_geometry"), [
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
                      ]),
                      g,
                    ),
                  )(g)
                },
                gen,
                @tactics.disch_tac,
                g => {
                  let all = block_under(
                    inst(thm("tlsf_small_partial_geometry"), [
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
                    ]),
                    g,
                  )
                  free_apply(
                    @bool.ispecl(
                      @list.List([tm(k), tm("(q : " + w + ")")]),
                      all,
                    ),
                  )(g)
                },
                arw([@lists.mem()]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
