// A cached allocation transfers one slot; physical memories and Page.used stay fixed.

///|
fn prove_tlsf_malloc_cached_models() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let n = malloc_cached_args(a, p, b, bs, k)
  let vs = page_model_variables() +
    [("p", w), ("b", w), ("bs", lw), ("k", "Num")]
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let s = a[9] + "(" + p + ")"
  let page = "tlsf_small_page_ok(" +
    [
      a[1],
      p,
      cap,
      s,
      a[10] + "(" + p + ")",
      a[11] + "(" + p + ")",
      a[12] + "(" + p + ")",
    ].join(",") +
    ")"
  let used = (a : Array[String], q : String) => {
    "tlsf_small_used(" + a[11] + "(" + q + ")," + a[12] + "(" + q + "))"
  }
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cond = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && " +
    block_lists(a) +
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
    s +
    " == 8*" +
    k +
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
    ")"
  let _ = lemma(
    "tlsf_malloc_cached_models",
    page_quantify(vs) +
    cond +
    " → " +
    block_backing(n) +
    " && " +
    block_lists(n),
    () => {
      seq([
        gen,
        strip,
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
          "tlsf_small_partition(" +
          [
            p,
            s,
            a[10] + "(" + p + ")",
            a[11] + "(" + p + ")",
            a[12] + "(" + p + ")",
          ].join(",") +
          ")",
          seq([
            @tactics.undisch_tac(tm(page)),
            rw([thm("tlsf_small_page_ok")]),
            page_publish_atomic([]),
          ]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_malloc_cached_partition"), [
                p,
                s,
                a[10] + "(" + p + ")",
                a[11] + "(" + p + ")",
                a[12] + "(" + p + ")",
                b,
              ]),
              g,
            ),
          )(g)
        },
        free_have(
          "∀ q : " + w + ", " + used(n, "q") + " == " + used(a, "q"),
          seq([
            gen,
            rw([thm("tlsf_small_put")]),
            @class.cond_cases_tac,
            subst_vars(),
            arw([]),
          ]),
        ),
        free_have(
          "tlsf_small_page_ok(" +
          [
            a[1],
            p,
            cap,
            s,
            a[10] + "(" + p + ")",
            "tlsf_small_remove(" + b + "," + a[11] + "(" + p + "))",
            "CONS(" + b + "," + a[12] + "(" + p + "))",
          ].join(",") +
          ")",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_small_partition(" +
                [
                  p,
                  s,
                  a[10] + "(" + p + ")",
                  "tlsf_small_remove(" + b + "," + a[11] + "(" + p + "))",
                  "CONS(" + b + "," + a[12] + "(" + p + "))",
                ].join(",") +
                ")",
              ),
            ),
            arw([]),
            @tactics.disch_tac,
            @tactics.undisch_tac(tm(page)),
            rw([thm("tlsf_small_page_ok")]),
            strip,
            arw([thm("tlsf_small_put")]),
            @tactics.undisch_tac(tm("MOD(" + s + ",8) == 0")),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        g => {
          let eq = @kernel.assume_rule(tm(s + " == 8*" + k))
          @tactics.rule_assum_tac(th => {
            if @kernel.concl(th) == @kernel.concl(eq) {
              th
            } else {
              @simp.rewrite_rule(ths([eq]))(th)
            }
          })(g)
        },
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.undisch_tac(tm(block_backing(a))),
              rw([thm("tlsf_small_backing")]),
              @tactics.disch_tac,
              rw([thm("tlsf_small_backing"), thm("tlsf_small_put")]),
              @tactics.x_gen_tac(tm("(q : " + w + ")")),
              strip,
              @class.asm_cases_tac(tm("(q : " + w + ") == " + p)),
              subst_vars(),
              arw([]),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(arw([])),
                  solve(
                    seq([
                      @tactics.first_assum(th => @logic.match_mp_tac(th)),
                      arw([]),
                    ]),
                  ),
                  solve(
                    seq([
                      @tactics.first_assum(th => {
                        @tactics.mp_tac(@bool.spec(tm("(q : " + w + ")"), th))
                      }),
                      arw([]),
                      page_publish_atomic([]),
                    ]),
                  ),
                  solve(
                    seq([
                      @tactics.first_assum(th => {
                        @tactics.mp_tac(@bool.spec(tm(p), th))
                      }),
                      arw([]),
                      page_publish_atomic([]),
                    ]),
                  ),
                ]),
              ),
            ]),
            seq([
              free_apply(
                inst(thm("tlsf_malloc_cached_lists"), a + [p, b, bs, k]),
              ),
              arw([]),
              gen,
              strip,
              free_apply(
                inst(
                  thm("tlsf_malloc_cached_other"),
                  a + [p, "(q : " + w + ")", b],
                ),
              ),
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
}
