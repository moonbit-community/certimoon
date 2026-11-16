// The last-release tail, specialized to each position in the partial list.

///|
fn prove_tlsf_block_free_tail_last_cases() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let model = page_model_variables()
  let basevs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let argv = basevs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let vs = basevs + [("a", lw), ("nx", w), ("tail", lw)]
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let current = block_after_release(args, p, b)
  let usage = block_usage(args, p)
  let total = block_total(args, p)
  let k = "DIV(" + args[9] + "(" + p + "),8)"
  let part = args[14] + "(" + k + ")"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let before = "st(NIL,[" +
    i(p) +
    "," +
    i("word(" + usage + ")") +
    ",(l2 : Value)]," +
    block_pending_rty(args, p, b, fp) +
    ")"
  let q = "tlsf_block_free_post(" + page_arguments(basevs) + ")"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let classify = inst(
    thm("tlsf_block_free_classify_pages"),
    ["(free_idx : Num)"] +
    current +
    [
      p,
      "(word(" + usage + ") : " + w + ")",
      "(l2 : Value)",
      block_large_frame(args, fp),
    ],
  )
  let ca = args_of(@basics.dest_imp(@kernel.concl(classify)).1, "sl_triple", 3).unwrap()
  let cs = args_of(ca[2], "st", 3).unwrap()
  let last = inst(thm("tlsf_block_free_last_test_raw"), [
    args[0],
    "(free_idx : Num)",
    p,
    "(word(" + usage + ") : " + w + ")",
    "(l2 : Value)",
    show(cs[2]),
  ])
  let lastq = args_of(@kernel.concl(last), "sl_triple", 3).unwrap()[2]
  let natives = block_native_hyp()
  for has_prev in [false, true] {
    for has_next in [false, true] {
      let a = if has_prev { "(a : " + lw + ")" } else { "(NIL : " + lw + ")" }
      let z = if has_next {
        "CONS((nx : " + w + "),(tail : " + lw + "))"
      } else {
        "(NIL : " + lw + ")"
      }
      let nx = if has_next {
        "(nx : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let pr = if has_prev {
        "tlsf_small_last((word(0) : " + w + ")," + a + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let split = part + " == APPEND(" + a + ",CONS(" + p + "," + z + "))"
      let label = (if has_prev { "prev" } else { "head" }) +
        "_" +
        (if has_next { "cons" } else { "nil" })
      let conditions = block_old_facts(args, p, b) +
        " && " +
        natives +
        " && " +
        usage +
        " == 1 && " +
        split +
        (if has_prev { " && !((a : " + lw + ") == NIL)" } else { "" })
      let _ = lemma(
        "tlsf_block_free_tail_last_" + label,
        "\{env}, \{page_quantify(vs)}\{conditions} → sl_triple_g(G,fs,tabs,inst,rp,\{before},tlsf_block_free_tail(d,free_idx),\{q},labels)",
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          block_prepare(args, p, b),
          free_have("!(" + usage + " == " + total + ")", @int.asm_arith_tac),
          free_have(usage + " < " + total, @int.asm_arith_tac),
          free_have(
            args[11] +
            "(" +
            p +
            ") == (NIL : " +
            lw +
            ") && tlsf_small_remove(" +
            b +
            "," +
            args[12] +
            "(" +
            p +
            ")) == NIL",
            small_meson(ths([])),
          ),
          free_have(
            current[12] + "(" + p + ") == (NIL : " + lw + ")",
            seq([
              rw([thm("tlsf_block_free_live"), thm("tlsf_small_put")]),
              arw([]),
            ]),
          ),
          free_have(
            "tlsf_count(" + p + "," + part + ") == 1",
            seq([
              @tactics.undisch_tac(tm(block_lists(args))),
              rw([thm("tlsf_small_lists_ok")]),
              small_meson(ths([])),
            ]),
          ),
          free_have(
            "!MEM(" + p + "," + a + ") && !MEM(" + p + "," + z + ")",
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_small_count_one_split"), [a, z, p]),
              ),
              @tactics.mp_tac(
                @kernel.assume_rule(
                  tm("tlsf_count(" + p + "," + part + ") == 1"),
                ),
              ),
              rw([@kernel.assume_rule(tm(split))]),
            ]),
          ),
          free_have(
            "tlsf_small_remove(" +
            p +
            "," +
            part +
            ") == APPEND(" +
            a +
            "," +
            z +
            ")",
            seq([
              rw([@kernel.assume_rule(tm(split))]),
              free_apply(inst(thm("tlsf_small_remove_split"), [a, z, p])),
            ]),
          ),
          if has_prev {
            seq([
              free_have(
                "MEM(" + pr + "," + a + ")",
                free_apply(inst(thm("tlsf_small_last_member"), [a])),
              ),
              free_have(
                "MEM(" + pr + "," + part + ")",
                seq([
                  rw([
                    @kernel.assume_rule(tm(split)),
                    @lists.mem_append(),
                    @lists.mem(),
                  ]),
                  arw([]),
                ]),
              ),
              free_have(
                "!(" +
                pr +
                " == (word(0) : " +
                w +
                ")) && val(" +
                pr +
                ")+32 <= 4294967296",
                small_meson(ths([])),
              ),
            ])
          } else {
            @tactics.all_tac
          },
          if has_next {
            seq([
              free_have(
                "MEM(" + nx + "," + part + ")",
                seq([
                  rw([
                    @kernel.assume_rule(tm(split)),
                    @lists.mem_append(),
                    @lists.mem(),
                  ]),
                  arw([]),
                ]),
              ),
              free_have(
                "!(" +
                nx +
                " == (word(0) : " +
                w +
                ")) && val(" +
                nx +
                ")+32 <= 4294967296",
                small_meson(ths([])),
              ),
            ])
          } else {
            @tactics.all_tac
          },
          g => {
            let remove = @kernel.assume_rule(
              tm(
                "tlsf_small_remove(" +
                p +
                "," +
                part +
                ") == APPEND(" +
                a +
                "," +
                z +
                ")",
              ),
            )
            let eqs = block_model_case("last", args, p, g).map(th => {
              @simp.rewrite_rule(ths([remove]))(th)
            })
            let models = @simp.rewrite_rule(ths(eqs))(
              block_under(inst(thm("tlsf_block_free_models"), args + [p, b]), g),
            )
            let reclaim = inst(
              thm("tlsf_block_free_reclaim_" + label + "_all"),
              [
                "(G : " + gt + ")",
                "(fs : List[Cl])",
                "(tabs : List[(Tab_t,List[V_ref])])",
                "(inst : Inst)",
                "(rp : " + sassn + ")",
                "(labels : List[" + sassn + "])",
                "(pop : Num)",
                "(push : Num)",
                "(free_idx : Num)",
              ] +
              current +
              [
                p,
                a,
                nx,
                "(tail : " + lw + ")",
                i("word(" + usage + ")"),
                "(l2 : Value)",
                fp,
              ],
            )
            let gate = @simp.rewrite_conv(
              ths([@kernel.assume_rule(tm(usage + " < " + total))]),
            )(tm(block_gate(args, p)))
            let firstFlag = block_flag(args, p, false, false, g)
            let lastFlag = block_flag(args, p, true, true, g)
            seq([
              @tactics.strip_assume_tac(models),
              rw([thm("tlsf_block_free_tail")]),
              @tactics.match_mp_tac(thm("sl_seq_g")),
              @tactics.exists_tac(ca[2]),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  block_g_conseq(classify, ent_tac([gate], []), same_tac()),
                  block_if(
                    false,
                    firstFlag,
                    seq([
                      rw([thm("tlsf_block_free_else")]),
                      @tactics.match_mp_tac(thm("sl_seq_g")),
                      @tactics.exists_tac(lastq),
                      @tactics.thenl(
                        @tactics.conj_tac,
                        @list.List([
                          free_lift(last),
                          block_if(
                            true,
                            lastFlag,
                            block_g_conseq(
                              reclaim,
                              ent_tac([], []),
                              block_returned_post(eqs, argv),
                            ),
                          ),
                        ]),
                      ),
                    ]),
                  ),
                ]),
              ),
            ])(g)
          },
        ]),
      )
    }
  }
}
