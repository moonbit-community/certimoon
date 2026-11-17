// Lift the page export to the complete backing and free-list model.

///|
fn prove_tlsf_page_publish_models() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let model = page_model_variables()
  let geometry = [3, 4, 8, 9, 10, 11, 12, 1, 13, 14].map(i => a[i])
  let _ = lemma(
    "tlsf_page_publish_backing_classes",
    page_quantify(model) +
    block_backing(a) +
    " → (∀ q : " +
    w +
    ", MEM(q," +
    a[8] +
    ") → 8 <= " +
    a[9] +
    "(q) && " +
    a[9] +
    "(q) <= 256 && MOD(" +
    a[9] +
    "(q),8) == 0 && DIV(" +
    a[9] +
    "(q),8) < 33)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
        strip,
        @tactics.x_gen_tac(tm("(q : " + w + ")")),
        @tactics.disch_tac,
        free_have(
          "8 <= " +
          a[9] +
          "((q : " +
          w +
          ")) && " +
          a[9] +
          "(q) <= 256 && MOD(" +
          a[9] +
          "(q),8) == 0",
          small_meson(ths([])),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_small_class_bounds"), [a[9] + "((q : " + w + "))"]),
        ),
        arw([]),
        small_meson(ths([])),
      ])
    },
  )
  for fresh in [false, true] {
    let s = if fresh { "(s : Num)" } else { a[9] + "(" + p + ")" }
    let oldLive = if fresh {
      "(NIL : " + lw + ")"
    } else {
      a[12] + "(" + p + ")"
    }
    let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
    let ready = "tlsf_small_page_ok(" +
      a[1] +
      "," +
      p +
      "," +
      cap +
      "," +
      s +
      ",CONS(" +
      b +
      "," +
      bs +
      "),NIL," +
      oldLive +
      ")"
    let postok = "tlsf_small_page_ok(" +
      a[1] +
      "," +
      p +
      "," +
      cap +
      "," +
      s +
      ",NIL," +
      bs +
      ",CONS(" +
      b +
      "," +
      oldLive +
      "))"
    let n = publish_args(a, p, b, bs, s, fresh)
    let k = "DIV(" + s + ",8)"
    let oldpart = a[14] + "(" + k + ")"
    let need = block_backing(a) +
      " && " +
      block_lists(a) +
      " && " +
      a[13] +
      "(" +
      k +
      ") == NIL && " +
      (if fresh {
        "!MEM(" +
        p +
        "," +
        a[8] +
        ") && MEM(" +
        p +
        "," +
        a[3] +
        ") && tlsf_used(" +
        a[4] +
        "(" +
        p +
        ")) && " +
        ready
      } else {
        "MEM(" +
        p +
        "," +
        a[8] +
        ") && " +
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
        ") == NIL && " +
        oldpart +
        " == CONS(" +
        p +
        ",(z : " +
        lw +
        "))"
      })
    let vs = model + [("p", w), ("b", w), ("bs", lw), ("s", "Num"), ("z", lw)]
    let oldPartEq = "∀ j : Num, j < 33 → " +
      n[14] +
      "(j) == tlsf_small_remove(" +
      p +
      "," +
      a[14] +
      "(j))"
    let _ = lemma(
      "tlsf_page_publish_" +
      (if fresh { "fresh" } else { "partial" }) +
      "_models",
      page_quantify(vs) +
      need +
      " → " +
      block_backing(n) +
      " && " +
      block_lists(n),
      () => {
        seq([
          gen,
          strip,
          g => {
            @tactics.assume_tac(
              block_under(inst(thm("tlsf_page_publish_backing_classes"), a), g),
            )(g)
          },
          free_have(
            "tlsf_count(" +
            p +
            "," +
            a[8] +
            ") == " +
            (if fresh { "0" } else { "1" }),
            if fresh {
              arw([thm("tlsf_count_zero")])
            } else {
              seq([
                @tactics.undisch_tac(tm(block_lists(a))),
                rw([thm("tlsf_small_lists_ok")]),
                strip,
                page_publish_old_page_facts(p),
                arw([]),
              ])
            },
          ),
          if fresh {
            @tactics.all_tac
          } else {
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_small_page_member_geometry"), geometry + [p]),
                  g,
                ),
              )(g)
            }
          },
          free_have(
            ready,
            if fresh {
              arw([])
            } else {
              seq([
                @tactics.undisch_tac(
                  tm(
                    "tlsf_small_page_ok(" +
                    [
                      a[1],
                      p,
                      cap,
                      a[9] + "(" + p + ")",
                      a[10] + "(" + p + ")",
                      a[11] + "(" + p + ")",
                      a[12] + "(" + p + ")",
                    ].join(",") +
                    ")",
                  ),
                ),
                arw([]),
              ])
            },
          ),
          free_have(
            "tlsf_small_partition(" +
            p +
            "," +
            s +
            ",CONS(" +
            b +
            "," +
            bs +
            "),NIL," +
            oldLive +
            ") && 8 <= " +
            s +
            " && " +
            s +
            " <= 256 && MOD(" +
            s +
            ",8) == 0",
            seq([
              @tactics.undisch_tac(tm(ready)),
              rw([thm("tlsf_small_page_ok")]),
              small_meson(ths([])),
            ]),
          ),
          split_conjs(),
          g => {
            @tactics.strip_assume_tac(
              block_under(
                inst(thm("tlsf_page_publish_partition"), [p, s, b, bs, oldLive]),
                g,
              ),
            )(g)
          },
          g => {
            let t = block_under(
              inst(thm("tlsf_page_publish_partition"), [p, s, b, bs, oldLive]),
              g,
            )
            @tactics.strip_assume_tac(
              @simp.rewrite_rule(ths([thm("tlsf_small_used"), @lists.length()]))(
                t,
              ),
            )(g)
          },
          g => {
            @tactics.strip_assume_tac(
              block_under(inst(thm("tlsf_small_class_bounds"), [s]), g),
            )(g)
          },
          g => {
            @tactics.strip_assume_tac(
              block_under(inst(thm("tlsf_small_capacity"), [s]), g),
            )(g)
          },
          free_have(
            postok,
            seq([
              @tactics.undisch_tac(tm(ready)),
              rw([thm("tlsf_small_page_ok")]),
              strip,
              arw([]),
            ]),
          ),
          free_have(
            "∀ q : " +
            w +
            ", MEM(q," +
            bs +
            ") → tlsf_count(q," +
            bs +
            ") == 1",
            seq([
              gen,
              @tactics.disch_tac,
              free_apply(
                inst(thm("tlsf_page_publish_cached_unique"), [
                  p,
                  s,
                  "(NIL : " + lw + ")",
                  bs,
                  "CONS(" + b + "," + oldLive + ")",
                  "(q : " + w + ")",
                ]),
              ),
            ]),
          ),
          if fresh {
            @tactics.all_tac
          } else {
            seq([
              free_have(
                "tlsf_small_used((NIL : " +
                lw +
                ")," +
                oldLive +
                ") < tlsf_small_total(" +
                s +
                ")",
                seq([
                  @tactics.undisch_tac(tm(ready)),
                  rw([
                    thm("tlsf_small_page_ok"),
                    thm("tlsf_small_partition"),
                    thm("tlsf_small_used"),
                    @lists.length(),
                  ]),
                  strip,
                  @int.asm_arith_tac,
                ]),
              ),
              free_have(
                "tlsf_count(" + p + "," + oldpart + ") == 1",
                seq([
                  @tactics.undisch_tac(tm(block_lists(a))),
                  rw([thm("tlsf_small_lists_ok")]),
                  strip,
                  page_publish_old_page_facts(p),
                  @tactics.first_assum(th => @logic.match_mp_tac(th)),
                  arw([]),
                ]),
              ),
              free_have(
                "!MEM(" + p + ",(z : " + lw + "))",
                seq([
                  @tactics.undisch_tac(
                    tm("tlsf_count(" + p + "," + oldpart + ") == 1"),
                  ),
                  arw([
                    thm("tlsf_small_count_cons"),
                    @equal.gsym(thm("tlsf_count_zero")),
                  ]),
                  @int.arith_tac,
                ]),
              ),
            ])
          },
          if fresh {
            @tactics.all_tac
          } else {
            g => {
              @tactics.assume_tac(
                block_under(
                  inst(thm("tlsf_small_remove_absent"), ["(z : " + lw + ")", p]),
                  g,
                ),
              )(g)
            }
          },
          free_have(
            oldPartEq,
            if fresh {
              seq([
                gen,
                @tactics.disch_tac,
                @tactics.conv_tac(@equal.sym_conv),
                free_apply(
                  inst(thm("tlsf_small_remove_absent"), [
                    a[14] + "((j : Num))",
                    p,
                  ]),
                ),
                @tactics.undisch_tac(tm(block_lists(a))),
                rw([thm("tlsf_small_lists_ok")]),
                small_meson(ths([])),
              ])
            } else {
              seq([
                gen,
                @tactics.disch_tac,
                g => {
                  let all = block_under(
                    inst(
                      thm("tlsf_small_partial_remove_class"),
                      a[8:].to_owned() + [p, b],
                    ),
                    g,
                  )
                  @tactics.mp_tac(
                    block_under(@bool.spec(tm("(j : Num)"), all), g),
                  )(g)
                },
                arw([
                  thm("tlsf_small_put_class"),
                  @lists.tl(),
                  thm("tlsf_small_remove_cons"),
                  thm("tlsf_small_remove_absent"),
                ]),
              ])
            },
          ),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              seq([
                @tactics.undisch_tac(tm(block_backing(a))),
                rw([thm("tlsf_small_backing")]),
                @tactics.disch_tac,
                rw([
                  thm("tlsf_small_backing"),
                  thm("tlsf_small_put"),
                  @lists.mem(),
                ]),
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                strip,
                @class.asm_cases_tac(tm("(q : " + w + ") == " + p)),
                subst_vars(),
                arw([]),
                free_at("publication backing update", small_meson(ths([]))),
              ]),
              seq([
                free_apply(
                  inst(
                    thm("tlsf_page_publish_lists"),
                    a[8:].to_owned() + n[8:].to_owned() + [p, s, bs, k],
                  ),
                ),
                rw([
                  thm("tlsf_small_put"),
                  thm("tlsf_small_put_class"),
                  @lists.mem(),
                  thm("tlsf_small_count_cons"),
                  thm("tlsf_small_used"),
                  @lists.length(),
                ]),
                arw([]),
                @tactics.repeat_tac(@tactics.conj_tac),
                free_at(
                  "publication list update",
                  @tactics.first(
                    @list.List([
                      solve(
                        seq([
                          gen,
                          @tactics.disch_tac,
                          have(
                            "!(" + p + " == (q : " + w + "))",
                            page_publish_atomic([]),
                          ),
                          @class.asm_cases_tac(tm("(q : " + w + ") == " + p)),
                          arw([@arith.add_clauses()]),
                          small_meson(ths([])),
                        ]),
                      ),
                      solve(seq([gen, @tactics.disch_tac, arw([])])),
                      solve(@int.asm_arith_tac),
                      solve(small_meson(ths([]))),
                    ]),
                  ),
                ),
              ]),
            ]),
          ),
        ])
      },
    )
  }
}
