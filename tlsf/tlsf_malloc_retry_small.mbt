// Focus one page and one table class around the compiled local triples.
// No old live payload enters the modified footprint.

///|
fn prove_tlsf_malloc_retry_publish_small() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let k = "DIV(" + s + ",8)"
  let z = "(z : " + lw + ")"
  let i32 = (x : String) => "V_num(ConstInt32((" + x + " : " + w + ")))"
  let pb = "word_add(" + b + ",word(8))"
  let p20 = "word_add(" + p + ",word(20))"
  let vs = page_model_variables() +
    [
      ("p", w),
      ("b", w),
      ("bs", lw),
      ("s", "Num"),
      ("i", "Num"),
      ("used0", w),
      ("prev0", w),
      ("l1", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
      ("fp", rty),
      ("z", lw),
    ]
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let own = (xs : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(xs + ["(fp : " + rty + ")(gs,ms)"])
  }
  for fresh in [true, false] {
    let n = publish_args(a, p, b, bs, s, fresh)
    let live = if fresh { "(NIL : " + lw + ")" } else { a[12] + "(" + p + ")" }
    let ready = "tlsf_small_page_ok(" +
      [
        a[1],
        p,
        cap,
        s,
        "CONS(" + b + "," + bs + ")",
        "(NIL : " + lw + ")",
        live,
      ].join(",") +
      ")"
    let init = "tlsf_page_allocate_build(" +
      [
        p,
        cap,
        s,
        "tlsf_small_total(" + s + ")",
        "(used0 : " + w + ")",
        "(prev0 : " + w + ")",
      ].join(",") +
      ")"
    let pre = own(
      (if fresh { [init] } else { [] }) + [block_pages(a), block_table(a)],
    )
    let post = own([
      block_pages(n),
      block_table(n),
      "tlsf_page_publish_payload(" + b + "," + s + ")",
    ])
    let lc = if fresh {
      "[" +
      i32(p) +
      "," +
      i32(b) +
      "," +
      i32("word(" + s + ")") +
      "," +
      i32(p20) +
      ",l4,(original : Value)]"
    } else {
      "[" +
      i32(p) +
      ",l1," +
      i32("word(" + s + ")") +
      ",l3,l4,(original : Value)]"
    }
    let pure = "val(" +
      a[0] +
      ") <= 4294965088 && " +
      ready +
      " && (i : Num) < tlsf_small_total(s) && b == tlsf_small_slot(p,s,i) && " +
      a[13] +
      "(" +
      k +
      ") == NIL && " +
      (if fresh {
        "!MEM(" +
        p +
        "," +
        a[8] +
        ") && REVERSE(tlsf_small_slots(p,s,tlsf_small_total(s))) == CONS(b,bs)"
      } else {
        "tlsf_count(" +
        p +
        "," +
        a[8] +
        ") == 1 && " +
        a[9] +
        "(" +
        p +
        ") == s && " +
        a[10] +
        "(" +
        p +
        ") == CONS(b,bs) && " +
        a[11] +
        "(" +
        p +
        ") == NIL && " +
        a[14] +
        "(" +
        k +
        ") == CONS(" +
        p +
        "," +
        z +
        ") && (∀ q : " +
        w +
        ", MEM(q," +
        z +
        ") → !(q == word(0)) && val(q)+32 <= 4294967296)"
      })
    let _ = lemma(
      "tlsf_malloc_retry_publish_" +
      (if fresh { "fresh" } else { "partial" }) +
      "_small",
      malloc_publication_quantify(vs) +
      pure +
      " → sl_triple(st(NIL," +
      lc +
      "," +
      pre +
      "),tlsf_malloc_retry_" +
      (if fresh { "fresh" } else { "partial" }) +
      "(d,initialize_idx,page_idx,take_idx,ensure_idx),(res : List[Value]) => (lc2 : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => lc2 == " +
      malloc_suffix_locals("retry", if fresh { "fresh" } else { "partial" }) +
      " && res == [" +
      i32(pb) +
      "] && (" +
      post +
      ")(gs,ms,h))",
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          "8 <= " + s + " && " + s + " <= 256 && MOD(" + s + ",8) == 0",
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
              malloc_publication_inst(thm("tlsf_small_class_bounds"), [s]),
              g,
            ),
          )(g)
        },
        free_have(
          "val(tlsf_base(" +
          a[0] +
          "))+1912+8*" +
          k +
          " == val(tlsf_base(" +
          a[0] +
          "))+1912+" +
          s,
          @int.asm_arith_tac,
        ),
        free_have(
          "val(tlsf_base(" +
          a[0] +
          "))+1916+8*" +
          k +
          " == val(tlsf_base(" +
          a[0] +
          "))+1916+" +
          s,
          @int.asm_arith_tac,
        ),
        g => {
          let focusOld = block_under(
            malloc_publication_inst(thm("tlsf_small_table_focus"), [
              a[0],
              a[13],
              a[14],
              k,
            ]),
            g,
          )
          let rest = args_of(@equal.rhs(@kernel.concl(focusOld)), "star", 2).unwrap()[1]
          let focusNew0 = block_under(
            malloc_publication_inst(thm("tlsf_small_table_focus"), [
              a[0],
              n[13],
              n[14],
              k,
            ]),
            g,
          )
          let restEq = malloc_publication_inst(
            thm("tlsf_page_publish_table_rest"),
            a +
            [
              p,
              b,
              bs,
              s,
              k,
              if fresh {
                a[14] + "(" + k + ")"
              } else {
                "TL(" + a[14] + "(" + k + "))"
              },
            ],
          )
          let restEq = @simp.rewrite_rule(
            ths([thm("tlsf_page_publish_put_class_same")]),
          )(restEq)
          let focusNew = @equal.conv_rule(
            @equal.rand_conv(@equal.subs_conv(ths([restEq]))),
            focusNew0,
          )
          let oldrest = a.copy()
          oldrest[8] = if fresh {
            a[8]
          } else {
            "tlsf_small_remove(" + p + "," + a[8] + ")"
          }
          let frameParts = [block_pages(oldrest), show(rest)]
          let cell = (a : String, x : String) => {
            "pts(" + a + ",serialise_i32((" + x + " : " + w + ")))"
          }
          let pt = "val(tlsf_base(" + a[0] + "))+1916+8*" + k
          let pathFrame = if fresh {
            own(
              frameParts +
              [
                cell(pt, "tlsf_small_head(" + a[14] + "(" + k + "))"),
                "tlsf_small_partial_links(word(0)," + a[14] + "(" + k + "))",
              ],
            )
          } else {
            own(frameParts)
          }
          let paths = if fresh {
            [
              malloc_publication_inst(
                thm("tlsf_malloc_retry_publish_fresh_page"),
                [
                  a[0],
                  a[1],
                  p,
                  cap,
                  s,
                  b,
                  bs,
                  live,
                  "(i : Num)",
                  "(used0 : " + w + ")",
                  "(prev0 : " + w + ")",
                  "(l1 : Value)",
                  "(l3 : Value)",
                  "(l4 : Value)",
                  pathFrame,
                ],
              ),
            ]
          } else {
            [false, true].map(hasNext => {
              malloc_publication_inst(
                thm(
                  "tlsf_malloc_retry_publish_partial_" +
                  (if hasNext { "cons" } else { "nil" }) +
                  "_page",
                ),
                [
                  a[0],
                  a[1],
                  p,
                  cap,
                  s,
                  b,
                  bs,
                  live,
                  "(i : Num)",
                  "(used0 : " + w + ")",
                  "(prev0 : " + w + ")",
                  "(l1 : Value)",
                  "(l3 : Value)",
                  "(l4 : Value)",
                  pathFrame,
                  if hasNext {
                    "(nextp : " + w + ")"
                  } else {
                    "(word(0) : " + w + ")"
                  },
                  if hasNext {
                    "(zs : " + lw + ")"
                  } else {
                    "(NIL : " + lw + ")"
                  },
                ],
              )
            })
          }
          let pagesNewRest = malloc_publication_inst(
            thm(
              "tlsf_page_publish_" +
              (if fresh { "fresh" } else { "partial" }) +
              "_pages_rest",
            ),
            a + [p, b, bs, s],
          )
          let pageNewFocus = if fresh {
            []
          } else {
            [
              block_under(
                malloc_publication_inst(thm("tlsf_small_pages_focus"), [
                  n[8],
                  n[4],
                  n[9],
                  n[10],
                  n[11],
                  n[12],
                  p,
                ]),
                g,
              ),
            ]
          }
          let pageOldFocus = if fresh {
            []
          } else {
            [
              block_under(
                malloc_publication_inst(thm("tlsf_small_pages_focus"), [
                  a[8],
                  a[4],
                  a[9],
                  a[10],
                  a[11],
                  a[12],
                  p,
                ]),
                g,
              ),
            ]
          }
          let before = [
              focusOld,
              thm("tlsf_small_table_item"),
              thm("tlsf_small_put"),
              thm("tlsf_small_head"),
              thm("tlsf_small_links"),
              @lists.mem(),
              @lists.hd(),
              @lists.not_cons_nil(),
            ] +
            pageOldFocus
          let after = [
              focusNew,
              thm("tlsf_small_table_item"),
              thm("tlsf_small_put"),
              thm("tlsf_small_put_class"),
              thm("tlsf_small_head"),
              thm("tlsf_small_links"),
              @lists.hd(),
              @lists.not_cons_nil(),
              @lists.tl(),
            ] +
            pageNewFocus
          let after = after +
            (if fresh { [thm("tlsf_small_pages_heap")] } else { [] })
          let run = (path : @kernel.Thm) => {
            seq([
              g => {
                let r = if fresh {
                  block_under(pagesNewRest, g)
                } else {
                  pagesNewRest
                }
                let r = @simp.rewrite_rule(
                  ths(g.0.to_array().map(t => t.1) + [thm("tlsf_small_put")]),
                )(r)
                @tactics.assume_tac(r)(g)
              },
              by_path(path, "T", before, [], after, []),
            ])
          }
          if fresh {
            run(paths[0])(g)
          } else {
            seq([
              @tactics.mp_tac(@bool.ispec(tm(z), @lists.list_cases())),
              @tactics.thenl(
                @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
                @list.List([
                  seq([subst_only("z"), run(paths[0])]),
                  seq([
                    @tactics.first_x_assum(th => {
                      if @basics.is_exists(@kernel.concl(th)) {
                        @tactics.x_choose_then(tm("(nextp : " + w + ")"))(
                          @tactics.x_choose_then(tm("(zs : " + lw + ")"))(th => {
                            @tactics.assume_tac(th)
                          }),
                        )(th)
                      } else {
                        @tactics.no_tac
                      }
                    }),
                    subst_only("z"),
                    free_have(
                      "!((nextp : " +
                      w +
                      ") == word(0)) && val(nextp)+32 <= 4294967296",
                      small_meson(ths([@lists.mem()])),
                    ),
                    run(paths[1]),
                  ]),
                ]),
              ),
            ])(g)
          }
        },
      ]),
    )
    let _ = argv
  }
}
