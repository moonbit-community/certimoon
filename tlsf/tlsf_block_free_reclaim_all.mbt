// Compose the compiled unlink prefix, argument load, and the closed compiled
// TLSF free call. The ambient specification supplies no helper assumptions.

///|
fn prove_tlsf_block_free_reclaim_all() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let model = page_model_variables()
  let arg = (n : String) => {
    let v = model.filter(v => v.0 == n)[0]
    "(" + v.0 + " : " + v.1 + ")"
  }
  let args = (ns : Array[String]) => ns.map(arg)
  let ba = args(["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"])
  let sa = args(["ps", "sz", "loc", "cached", "live", "fast", "partial"])
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = page_quantify(model + [("p", w)])
  let subback = lemma(
    "tlsf_small_backing_remove_domain",
    "\{vars} tlsf_small_backing(\{ba.join(",")}) → tlsf_small_backing(" +
    ([ba[0], ba[1], "tlsf_small_remove((p : " + w + ")," + ba[2] + ")"] +
    ba[3:].to_owned()).join(",") +
    ")",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_backing"), thm("tlsf_small_remove_member")]),
        strip,
        gen,
        strip,
        small_meson(ths([])),
      ])
    },
  )
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let vs = page_quantify(
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
  let s = arg("sz") + "((p : " + w + "))"
  let k = "DIV(" + s + ",8)"
  let current = "tlsf_small_pages_heap(" +
    args(["ps", "hd", "sz", "loc", "cached", "live"]).join(",") +
    ")"
  let table = "tlsf_small_table(" +
    args(["d", "fast", "partial"]).join(",") +
    ")"
  let large = "tlsf_large(" + page_arguments(model[:8].to_owned()) + ")"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{large},(fp : \{rty})(gs,ms),h)"
  let preR = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{small_star([large,current,table,"(fp : "+rty+")(gs,ms)"])}(h)"
  let before = "st(NIL,[\{i("p")},(u : Value),(l2 : Value)],\{preR})"
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
      let pages = "tlsf_small_remove((p : " + w + ")," + arg("ps") + ")"
      let partial = "tlsf_small_put_class(" +
        arg("partial") +
        "," +
        k +
        ",APPEND(" +
        a +
        "," +
        z +
        "))"
      let remaining = model.map(v => {
        if v.0 == "ps" {
          pages
        } else if v.0 == "partial" {
          partial
        } else {
          "(" + v.0 + " : " + v.1 + ")"
        }
      })
      let lc = "[" +
        i("p") +
        "," +
        i(nx) +
        "," +
        i(if has_prev { pr } else { "word(" + k + ")" }) +
        "]"
      let returnCall = inst(
        thm("tlsf_small_return_all"),
        [
          "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)",
          "(pop : Num)", "(push : Num)", "(free_idx : Num)",
        ] +
        remaining +
        ["(p : " + w + ")", "(fp : " + rty + ")", "(NIL : List[Value])", lc],
      )
      let ant = @basics.dest_imp(@kernel.concl(returnCall)).0
      let natives = show(@basics.dest_conj(@basics.dest_conj(ant).1).1)
      let callargs = args_of(
        @basics.dest_imp(@kernel.concl(returnCall)).1,
        "sl_triple_m",
        7,
      ).unwrap()
      let unlink = inst(
        thm(
          "tlsf_block_free_reclaim_" +
          (if has_prev { "prev" } else { "head" }) +
          "_" +
          (if has_next { "cons" } else { "nil" }) +
          "_pages",
        ),
        ["(free_idx : Num)"] +
        model.map(v => "(" + v.0 + " : " + v.1 + ")") +
        [
          "(p : " + w + ")",
          a,
          nx,
          "(tail : " + lw + ")",
          "(u : Value)",
          "(l2 : Value)",
          frame,
        ],
      )
      let uq = args_of(
          @basics.dest_imp(@kernel.concl(unlink)).1,
          "sl_triple",
          3,
        ).unwrap()[2]
      let rr = args_of(uq, "st", 3).unwrap()[2]
      let get = inst(thm("tlsf_free_publish_arg"), [
        "(p : " + w + ")",
        i(nx),
        i(if has_prev { pr } else { "word(" + k + ")" }),
        show(rr),
      ])
      let listsRemaining = "tlsf_small_lists_ok(" +
        [pages, sa[1], sa[2], sa[3], sa[4], sa[5], partial].join(",") +
        ")"
      let cond = "tlsf_small_backing(" +
        ba.join(",") +
        ") && MEM((p : " +
        w +
        ")," +
        arg("ps") +
        ") && tlsf_count(p,ps) == 1 && " +
        arg("cached") +
        "(p) == NIL && " +
        arg("live") +
        "(p) == NIL && val((d : " +
        w +
        ")) <= 4294965088 && " +
        arg("partial") +
        "(" +
        k +
        ") == " +
        old +
        " && " +
        listsRemaining +
        " && " +
        natives +
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
        "tlsf_block_free_reclaim_" + label + "_all",
        "\{env}, \{vs} \{cond} → sl_triple_g(G,fs,tabs,inst,rp,\{before},tlsf_block_free_reclaim(d,free_idx),\{show(callargs[5])},labels)",
        () => {
          seq([
            gen,
            strip,
            @tactics.assume_tac(
              @simp.rewrite_rule(ths([@lists.append()]))(
                @kernel.assume_rule(tm(listsRemaining)),
              ),
            ),
            g => {
              @tactics.assume_tac(
                block_under(
                  inst(
                    subback,
                    model.map(v => "(" + v.0 + " : " + v.1 + ")") +
                    ["(p : " + w + ")"],
                  ),
                  g,
                ),
              )(g)
            },
            free_have(
              "!MEM((p : \{w}),tlsf_small_remove(p,(ps : \{lw})))",
              rw([thm("tlsf_small_remove_member")]),
            ),
            free_have(
              "MEM((p : \{w}),(xs : \{lw})) && tlsf_used((hd : (\{w}) -> \{w})(p))",
              seq([
                @tactics.undisch_tac(
                  tm("tlsf_small_backing(" + ba.join(",") + ")"),
                ),
                rw([thm("tlsf_small_backing")]),
                small_meson(ths([])),
              ]),
            ),
            rw([thm("tlsf_block_free_reclaim_parts")]),
            @tactics.match_mp_tac(thm("sl_seq_g")),
            @tactics.exists_tac(uq),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                free_at(
                  "reclaim unlink",
                  free_g_conseq(
                    unlink,
                    free_at("reclaim unlink pre", ent_tac([], [])),
                    same_tac(),
                  ),
                ),
                seq([
                  @tactics.match_mp_tac(thm("sl_cons_g")),
                  @tactics.exists_tac(callargs[3]),
                  @tactics.thenl(
                    @tactics.conj_tac,
                    @list.List([
                      free_at(
                        "reclaim arg",
                        block_g_conseq(
                          get,
                          same_tac(),
                          free_at(
                            "reclaim arg post",
                            ent_tac(
                              [
                                thm("tlsf_free_pre"),
                                thm("tlsf_small"),
                                thm("tlsf_small_remove_member"),
                                @lists.append(),
                              ],
                              [],
                            ),
                          ),
                        ),
                      ),
                      free_at("reclaim call", free_lift(returnCall)),
                    ]),
                  ),
                ]),
              ]),
            ),
          ])
        },
      )
    }
  }
}
