// The full-page and ordinary partial-page tails use the verified classifier,
// publish operation, and unchanged-heap test/constant fragments.

///|
fn prove_tlsf_block_free_tail_stable() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let params = page_arguments(vs)
  let argv = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let current = block_after_release(args, p, b)
  let usage = block_usage(args, p)
  let total = block_total(args, p)
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[" + i(p) + "," + i("word(" + usage + ")") + ",(l2 : Value)]"
  let before = "st(NIL," + lc + "," + block_pending_rty(args, p, b, fp) + ")"
  let q = "tlsf_block_free_post(" + params + ")"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let natives = block_native_hyp()
  for full in [true, false] {
    let branch = if full {
      usage + " == " + total
    } else {
      "!(" + usage + " == " + total + ") && !(" + usage + " == 1)"
    }
    let conditions = block_old_facts(args, p, b) +
      " && " +
      natives +
      " && " +
      branch
    let classFrame = if full {
      "(gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => ms == " +
      args[1] +
      " && " +
      small_star([
        block_large(args),
        "tlsf_bytes(val(" + p + ")+24,8)",
        fp + "(gs,ms)",
      ]) +
      "(h)"
    } else {
      block_large_frame(args, fp)
    }
    let classify = inst(
      thm("tlsf_block_free_classify_pages"),
      ["(free_idx : Num)"] +
      current +
      [p, "(word(" + usage + ") : " + w + ")", "(l2 : Value)", classFrame],
    )
    let ca = args_of(
      @basics.dest_imp(@kernel.concl(classify)).1,
      "sl_triple",
      3,
    ).unwrap()
    let st = args_of(ca[2], "st", 3).unwrap()
    let rr = show(st[2])
    let publish = inst(
      thm("tlsf_block_free_publish_pages"),
      ["(free_idx : Num)"] +
      current +
      [p, i("word(" + usage + ")"), "(l2 : Value)", block_large_frame(args, fp)],
    )
    let last = inst(thm("tlsf_block_free_last_test_raw"), [
      args[0],
      "(free_idx : Num)",
      p,
      "(word(" + usage + ") : " + w + ")",
      "(l2 : Value)",
      rr,
    ])
    let lastq = args_of(@kernel.concl(last), "sl_triple", 3).unwrap()[2]
    let zero = inst(thm("tlsf_block_free_zero"), [lc, rr])
    let _ = lemma(
      "tlsf_block_free_tail_" + (if full { "full" } else { "partial" }),
      "\{env}, \{page_quantify(vs)}\{conditions} → sl_triple_g(G,fs,tabs,inst,rp,\{before},tlsf_block_free_tail(d,free_idx),\{q},labels)",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          block_prepare(args, p, b),
          if full {
            free_have("!(" + usage + " == 1)", @int.asm_arith_tac)
          } else {
            free_have(usage + " < " + total, @int.asm_arith_tac)
          },
          g => {
            let eqs = block_model_case(
              if full {
                "full"
              } else {
                "partial"
              },
              args,
              p,
              g,
            )
            let flag = block_flag(args, p, false, full, g)
            let gate = @simp.rewrite_conv(
              ths(
                if full {
                  [
                    @kernel.assume_rule(tm(usage + " == " + total)),
                    @arith.lt_refl(),
                  ]
                } else {
                  [@kernel.assume_rule(tm(usage + " < " + total))]
                },
              ),
            )(tm(block_gate(args, p)))
            let finish = if full {
              block_g_conseq(
                publish,
                ent_tac([], []),
                block_same_post(eqs, argv),
              )
            } else {
              seq([
                rw([thm("tlsf_block_free_else")]),
                @tactics.match_mp_tac(thm("sl_seq_g")),
                @tactics.exists_tac(lastq),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    free_lift(last),
                    block_if(
                      false,
                      block_flag(args, p, true, false, g),
                      block_g_conseq(
                        zero,
                        same_tac(),
                        block_same_post(eqs, argv),
                      ),
                    ),
                  ]),
                ),
              ])
            }
            seq([
              rw([thm("tlsf_block_free_tail")]),
              @tactics.match_mp_tac(thm("sl_seq_g")),
              @tactics.exists_tac(ca[2]),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  block_g_conseq(classify, ent_tac([gate], []), same_tac()),
                  block_if(full, flag, finish),
                ]),
              ),
            ])(g)
          },
        ])
      },
    )
  }
}
