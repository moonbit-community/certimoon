// Unlink an empty page and reassemble its complete payload, retaining all
// remaining page heaps and every byte in the client frame.

///|
fn prove_tlsf_block_free_reclaim_pages() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let model = page_model_variables()
  let arg = (n : String) => {
    let v = model.filter(v => v.0 == n)[0]
    "(" + v.0 + " : " + v.1 + ")"
  }
  let args = (ns : Array[String]) => ns.map(arg)
  let pa = args(["ps", "hd", "sz", "loc", "cached", "live"])
  let ba = args(["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"])
  let geo = args([
    "xs", "hd", "ps", "sz", "loc", "cached", "live", "lim", "fast", "partial",
  ])
  let s = arg("sz") + "((p : " + w + "))"
  let k = "DIV(" + s + ",8)"
  let cap = "val(tlsf_size(" + arg("hd") + "((p : " + w + "))))"
  let loc = arg("loc") + "((p : " + w + "))"
  let pages = "tlsf_small_pages_heap(" + pa.join(",") + ")"
  let rest = "tlsf_small_pages_heap(tlsf_small_remove((p : " +
    w +
    ")," +
    pa[0] +
    ")," +
    pa[1:].to_owned().join(",") +
    ")"
  let tail = "tlsf_block_free_page_tail((p : " +
    w +
    ")," +
    cap +
    "," +
    s +
    "," +
    loc +
    ",(NIL : " +
    lw +
    "),(NIL : " +
    lw +
    "))"
  let table = "tlsf_small_table(" +
    args(["d", "fast", "partial"]).join(",") +
    ")"
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let frame = own([tail, rest])
  let pre = own([pages, table])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
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
  let nilca = arg("cached") + "((p : " + w + ")) == (NIL : " + lw + ")"
  let nilli = arg("live") + "((p : " + w + ")) == (NIL : " + lw + ")"
  let vars = page_quantify(
    model +
    [
      ("p", w),
      ("a", lw),
      ("nx", w),
      ("tail", lw),
      ("u", "Value"),
      ("l2", "Value"),
      ("fp", rty),
    ],
  )
  for has_prev in [false, true] {
    for has_next in [false, true] {
      let a = if has_prev { "(a : " + lw + ")" } else { "(NIL : " + lw + ")" }
      let z = if has_next {
        "CONS((nx : " + w + "),(tail : " + lw + "))"
      } else {
        "(NIL : " + lw + ")"
      }
      let pr = if has_prev {
        "tlsf_small_last((word(0) : " + w + ")," + a + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let nx = if has_next {
        "(nx : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let old = "APPEND(" + a + ",CONS((p : " + w + ")," + z + "))"
      let entries = "APPEND(" + a + "," + z + ")"
      let updated = "tlsf_small_put_class(" +
        arg("partial") +
        "," +
        k +
        "," +
        entries +
        ")"
      let table2 = "tlsf_small_table(" +
        args(["d", "fast"]).join(",") +
        "," +
        updated +
        ")"
      let post = own([
        "tlsf_bytes(val((p : " + w + "))+8," + cap + ")",
        rest,
        table2,
      ])
      let cond = "tlsf_small_backing(" +
        ba.join(",") +
        ") && MEM((p : " +
        w +
        ")," +
        pa[0] +
        ") && tlsf_count(p,ps) == 1 && " +
        nilca +
        " && " +
        nilli +
        " && val((d : " +
        w +
        ")) <= 4294965088 && " +
        arg("partial") +
        "(" +
        k +
        ") == " +
        old +
        (if has_prev {
          " && !((a : " +
          lw +
          ") == NIL) && !((" +
          pr +
          ") == word(0)) && val(" +
          pr +
          ")+32 <= 4294967296"
        } else {
          ""
        }) +
        (if has_next {
          " && !((nx : " + w + ") == word(0)) && val(nx)+32 <= 4294967296"
        } else {
          ""
        })
      let label = (if has_prev { "prev" } else { "head" }) +
        "_" +
        (if has_next { "cons" } else { "nil" })
      let _ = lemma(
        "tlsf_block_free_reclaim_" + label + "_pages",
        "∀ free_idx : Num, \{vars} \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_unlink(d,free_idx),st(NIL,[\{i("p")},\{i(nx)},\{i(if has_prev { pr } else { "word("+k+")" })}],\{post}))",
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            @tactics.strip_assume_tac(
              block_under(
                inst(
                  thm("tlsf_small_page_member_geometry"),
                  geo + ["(p : " + w + ")"],
                ),
                g,
              ),
            )(g)
          },
          g => {
            let focus0 = block_under(
              inst(thm("tlsf_small_pages_focus"), pa + ["(p : " + w + ")"]),
              g,
            )
            let nf = [
              @kernel.assume_rule(tm(nilca)),
              @kernel.assume_rule(tm(nilli)),
              thm("tlsf_small_page_size_focus"),
            ]
            let focus = @equal.conv_rule(
              @equal.rand_conv(@simp.rewrite_conv(ths(nf))),
              focus0,
            )
            let path = inst(
              thm("tlsf_block_free_unlink_" + label + "_table"),
              args(["d"]) +
              ["(free_idx : Num)"] +
              args(["fast", "partial"]) +
              [
                "(p : " + w + ")",
                s,
                a,
                nx,
                "(tail : " + lw + ")",
                "(u : Value)",
                "(l2 : Value)",
                frame,
              ],
            )
            let postTac = seq([
              gen,
              rw([thm("st")]),
              beta_goal(),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              arw([]),
              g => {
                let client = small_star([
                  rest,
                  table2,
                  "(fp : " + rty + ")((gs : List[Value]),(ms : Num))",
                ])
                let geom = "tlsf_small_page_ok((lim : Num),(p : " +
                  w +
                  ")," +
                  cap +
                  "," +
                  s +
                  "," +
                  loc +
                  ",(NIL : " +
                  lw +
                  "),(NIL : " +
                  lw +
                  "))"
                let recover = inst(thm("tlsf_small_recover_page"), [
                  "(lim : Num)",
                  "(p : " + w + ")",
                  cap,
                  s,
                  loc,
                  pr,
                  nx,
                  client,
                ])
                seq([
                  free_have(
                    geom,
                    seq([
                      @tactics.undisch_tac(
                        tm(
                          "tlsf_small_page_ok((lim : Num),(p : " +
                          w +
                          ")," +
                          cap +
                          "," +
                          s +
                          "," +
                          loc +
                          "," +
                          arg("cached") +
                          "(p)," +
                          arg("live") +
                          "(p))",
                        ),
                      ),
                      arw([]),
                    ]),
                  ),
                  g => {
                    @tactics.match_mp_tac(
                      @bool.spec(
                        tm("(h : " + heap + ")"),
                        block_under(recover, g),
                      ),
                    )(g)
                  },
                  @tactics.first_x_assum(th => {
                    if head_name(@kernel.concl(th)) == "star" {
                      @tactics.mp_tac(th)
                    } else {
                      @tactics.no_tac
                    }
                  }),
                  rw([thm("tlsf_small_page_size_focus")] + ac),
                  arw([]),
                ])(g)
              },
            ])
            page_conseq(path, ent_tac([focus], []), postTac)(g)
          },
        ]),
      )
    }
  }
}
