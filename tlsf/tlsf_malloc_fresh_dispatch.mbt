///|
fn prove_tlsf_malloc_fresh_dispatch() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let slots = "REVERSE(tlsf_small_slots(" +
    p +
    "," +
    s +
    ",tlsf_small_total(" +
    s +
    ")))"
  let geom = "tlsf_page_allocate_geometry(" + p + "," + cap + "," + s + ")"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let ready = publish_ready(a, p, b, bs, s, "(NIL : " + lw + ")")
  let need = slots +
    " == CONS(" +
    b +
    "," +
    bs +
    ") && " +
    ready +
    " && (i : Num) < tlsf_small_total(" +
    s +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    s +
    ",i) && !(" +
    b +
    " == word(0))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_fresh_dispatch",
    page_quantify(page_model_variables() + [("p", w), ("s", "Num")]) +
    physical +
    " && MEM(" +
    p +
    "," +
    a[3] +
    ") && " +
    geom +
    " → (∃ b : " +
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
          "val(" +
          p +
          ")+8+" +
          cap +
          " <= " +
          a[1] +
          " && " +
          a[1] +
          " <= 4294967296",
          seq([
            @tactics.undisch_tac(tm(physical)),
            rw([thm("tlsf_physical_ok")]),
            strip,
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
                    p,
                  ]),
                  g,
                ),
              )(g)
            },
            @tactics.undisch_tac(
              tm(
                "tlsf_block_ok(val(" +
                p +
                ")," +
                a[1] +
                "," +
                p +
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
        g => {
          @tactics.assume_tac(
            block_under(
              inst(thm("tlsf_page_publish_fresh_ready"), [p, cap, s, a[1]]),
              g,
            ),
          )(g)
        },
        free_have(
          "8 <= " + s + " && " + s + " <= 256 && MOD(" + s + ",8) == 0",
          seq([
            @tactics.undisch_tac(tm(geom)),
            rw([thm("tlsf_page_allocate_geometry")]),
            page_publish_atomic([]),
          ]),
        ),
        split_conjs(),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_capacity"), [s]), g),
          )(g)
        },
        free_have(
          "!(" + slots + " == NIL)",
          seq([
            rw([
              @equal.gsym(@lists.length_eq_nil()),
              @lists.length_reverse(),
              thm("tlsf_small_slots_length"),
            ]),
            @int.asm_arith_tac,
          ]),
        ),
        @tactics.mp_tac(@bool.ispec(tm(slots), @lists.list_cases())),
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
                free_have(
                  ready,
                  seq([
                    @tactics.undisch_tac(
                      tm(
                        "tlsf_small_page_ok(" +
                        [
                          a[1],
                          p,
                          cap,
                          s,
                          slots,
                          "(NIL : " + lw + ")",
                          "(NIL : " + lw + ")",
                        ].join(",") +
                        ")",
                      ),
                    ),
                    arw([]),
                  ]),
                ),
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
                        "(NIL : " + lw + ")",
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
                        "CONS(" + b + "," + bs + ")",
                        "(NIL : " + lw + ")",
                        "(NIL : " + lw + ")",
                        "(i : Num)",
                      ]),
                      g,
                    ),
                  )(g)
                },
                @tactics.exists_tac(tm(b)),
                @tactics.exists_tac(tm(bs)),
                @tactics.exists_tac(tm("(i : Num)")),
                arw([]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
