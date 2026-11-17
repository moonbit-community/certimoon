// Closed publication triples: complete allocator ownership is restored and
// the returned payload is transferred to the caller alongside its frame.

///|
fn prove_tlsf_page_publish_all() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let vs = publish_vars()
  let av = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let fp = "(fp : " + rty + ")"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let k = "DIV(" + s + ",8)"
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
  for fresh in [true, false] {
    let tag = if fresh { "fresh" } else { "partial" }
    let pre = "tlsf_page_publish_" + tag + "_pre(" + av.join(",") + ")"
    let post = "tlsf_page_publish_" + tag + "_post(" + av.join(",") + ")"
    let ready = publish_ready(
      a,
      p,
      b,
      bs,
      s,
      if fresh {
        "(NIL : " + lw + ")"
      } else {
        a[12] + "(" + p + ")"
      },
    )
    let lf = block_large_frame(a, fp)
    let smallArgs = a +
      [
        p,
        b,
        bs,
        s,
        "(i : Num)",
        "(used0 : " + w + ")",
        "(prev0 : " + w + ")",
        "(l1 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
        lf,
        "(z : " + lw + ")",
      ]
    let path = inst(thm("tlsf_page_publish_" + tag + "_small"), smallArgs)
    let parts = args_of(@basics.dest_imp(@kernel.concl(path)).1, "sl_triple", 3).unwrap()
    let f = show(@basics.dest_imp(@kernel.concl(path)).0) +
      " && " +
      block_backing(a) +
      " && " +
      block_lists(a) +
      " && " +
      (if fresh {
        "MEM(" + p + "," + a[3] + ") && tlsf_used(" + a[4] + "(" + p + "))"
      } else {
        "MEM(" + p + "," + a[8] + ")"
      })
    let mid = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => (∃ i : Num, (" +
      f +
      ") && (" +
      show(parts[0]) +
      ")(vs,lc,gs,ms,h))"
    let geometry = [3, 4, 8, 9, 10, 11, 12, 1, 13, 14].map(i => a[i])
    let preEnt = seq([
      gen,
      beta_goal(),
      rw(
        [
          thm("tlsf_page_publish_" + tag + "_pre"),
          thm("tlsf_allocator_frame"),
          thm("tlsf_small"),
        ] +
        lift_rws(),
      ),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
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
        "8 <= " + s + " && " + s + " <= 256 && MOD(" + s + ",8) == 0",
        seq([
          @tactics.undisch_tac(tm(ready)),
          rw([thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      split_conjs(),
      free_have(
        "val(" + a[0] + ") <= 4294965088",
        seq([
          @tactics.match_mp_tac(
            inst(
              thm("tlsf_block_free_large_bound"),
              a +
              [
                small_star(
                  [block_pages(a), block_table(a)] +
                  (if fresh {
                    [
                      "tlsf_page_allocate_build(" +
                      [
                        p,
                        cap,
                        s,
                        "tlsf_small_total(" + s + ")",
                        "(used0 : " + w + ")",
                        "(prev0 : " + w + ")",
                      ].join(",") +
                      ")",
                    ]
                  } else {
                    []
                  }) +
                  ["(" + fp + ")((gs : List[Value]),(ms : Num))"],
                ),
                "(h : " + heap + ")",
              ],
            ),
          ),
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "star" {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          arw(ac),
        ]),
      ),
      if fresh {
        @tactics.all_tac
      } else {
        seq([
          free_have(
            "tlsf_count(" + p + "," + a[8] + ") == 1",
            seq([
              @tactics.undisch_tac(tm(block_lists(a))),
              rw([thm("tlsf_small_lists_ok")]),
              small_meson(ths([])),
            ]),
          ),
          free_have(
            "∀ q : " +
            w +
            ", MEM(q,(z : " +
            lw +
            ")) → !(q == word(0)) && val(q)+32 <= 4294967296",
            seq([
              g => {
                @tactics.assume_tac(
                  block_under(
                    inst(thm("tlsf_small_partial_geometry"), geometry),
                    g,
                  ),
                )(g)
              },
              g => {
                @tactics.strip_assume_tac(
                  block_under(inst(thm("tlsf_small_class_bounds"), [s]), g),
                )(g)
              },
              gen,
              @tactics.disch_tac,
              free_have(
                "MEM((q : " + w + ")," + a[14] + "(" + k + "))",
                seq([arw([@lists.mem()])]),
              ),
              small_meson(ths([])),
            ]),
          ),
        ])
      },
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
              if fresh {
                "(NIL : " + lw + ")"
              } else {
                a[12] + "(" + p + ")"
              },
            ]),
            g,
          ),
        )(g)
      },
      @tactics.exists_tac(tm("(i : Num)")),
      arw([thm("st")] + lift_rws() + ac),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(ac),
    ])
    let postEnt = seq([
      gen,
      beta_goal(),
      rw(
        [
          thm("tlsf_page_publish_" + tag + "_post"),
          thm("tlsf_allocator_frame"),
          thm("tlsf_small"),
        ] +
        lift_rws(),
      ),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        let model = block_under(
          inst(
            thm("tlsf_page_publish_" + tag + "_models"),
            a + [p, b, bs, s, "(z : " + lw + ")"],
          ),
          g,
        )
        let model = @simp.rewrite_rule(g.0.map(t => t.1))(model)
        @tactics.strip_assume_tac(model)(g)
      },
      arw([]),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(ac),
    ])
    let ordinary = lemma(
      "tlsf_page_publish_" + tag + "_allocator",
      page_quantify(vs) +
      "sl_triple(" +
      pre +
      ",tlsf_page_publish_" +
      tag +
      "_code(d)," +
      post +
      ")",
      seq([
        gen,
        @tactics.match_mp_tac(thm("sl_conseq")),
        @tactics.exists_tac(tm(mid)),
        @tactics.exists_tac(tm(post)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_at("publication entry", preEnt),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                free_at(
                  "publication body",
                  seq([
                    @tactics.match_mp_tac(thm("sl_ex")),
                    beta_goal(),
                    @tactics.x_gen_tac(tm("(i : Num)")),
                    @tactics.match_mp_tac(thm("sl_pure")),
                    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                    @tactics.match_mp_tac(thm("sl_conseq")),
                    @tactics.exists_tac(parts[0]),
                    @tactics.exists_tac(parts[2]),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        same_tac(),
                        @tactics.thenl(
                          @tactics.conj_tac,
                          @list.List([
                            free_apply(path),
                            free_at("publication allocator fold", postEnt),
                          ]),
                        ),
                      ]),
                    ),
                  ]),
                ),
                same_tac(),
              ]),
            ),
          ]),
        ),
      ]),
    )
    let _ = lemma(
      "tlsf_page_publish_" + tag + "_all",
      "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, " +
      page_quantify(vs) +
      "sl_triple_m(fs,tabs,inst," +
      pre +
      ",tlsf_page_publish_" +
      tag +
      "_code(d)," +
      post +
      ",NIL)",
      seq([
        gen,
        @tactics.match_mp_tac(thm("sl_triple_m_of")),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            call_free_tac(),
            seq([
              @tactics.match_mp_tac(thm("sl_triple_l_of")),
              @tactics.match_accept_tac(ordinary),
            ]),
          ]),
        ),
      ]),
    )
  }
}
