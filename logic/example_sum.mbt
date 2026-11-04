// example_sum: a loop on locals that adds n0 + ... + 1 to acc0.
//
//   local.get 0
//   if
//     loop
//       local.get 1; local.get 0; i32.add; local.set 1   ;; acc += n
//       local.get 0; i32.const 1; i32.sub; local.set 0   ;; n -= 1
//       local.get 0; br_if 0                             ;; again if n ≠ 0
//     end
//   end
//
// from locals [n0, acc0] ends with [0, acc0 + sum_to(n0)] (as words). The
// loop's invariant: the locals are [n, acc] with n ≠ 0 and acc +
// sum_to(n) the answer. The proof runs the body's straight-line part with
// the st_ rules, then br_if 0 (sl_br_if: back to the loop with the
// invariant, or out with n = 0), and builds the loop, the block and the
// if around it.

///|
/// The parts (p, bs, q, ls) of `sl_triple_l(p, bs, q, ls)`.
fn triple_l_parts(
  th : @kernel.Thm,
) -> (@kernel.Term, @kernel.Term, @kernel.Term, @kernel.Term) raise {
  triple_l_terms(@kernel.concl(th))
}

///|
fn triple_l_terms(
  t : @kernel.Term,
) -> (@kernel.Term, @kernel.Term, @kernel.Term, @kernel.Term) raise {
  let (_, args) = @basics.strip_comb(t)
  guard args.to_array() is [p, bs, q, ls] else {
    raise Failure("wasmcert/logic: not a triple with labels: " + show(t))
  }
  (p, bs, q, ls)
}

///|
/// `rule` applied to `args` (in the term syntax), with `norm`.
fn inst(rule : String, args : Array[String]) -> @kernel.Thm raise {
  norm(@bool.ispecl(@list.List(args.map(tm)), thm(rule)))
}

///|
/// a then b (both sl_triple, or both sl_triple_l with `rule` sl_seq_l):
/// a's postcondition must be b's precondition.
fn glue(a : @kernel.Thm, b : @kernel.Thm, rule? : String = "sl_seq") -> @kernel.Thm raise {
  norm(@drule.match_mp(thm(rule))(@bool.conj(a, b))) catch {
    e => {
      let (_, args_a) = @basics.strip_comb(@kernel.concl(a))
      let (_, args_b) = @basics.strip_comb(@kernel.concl(b))
      raise Failure(
        "wasmcert/logic: glue: " + show(args_a.to_array()[2]) + " is not " + show(args_b.to_array()[0]) +
        " (" + e.to_string() + ")",
      )
    }
  }
}

///|
/// The sl_triple `th` as an sl_triple_l with labels `ls`.
fn with_labels(th : @kernel.Thm, ls : @kernel.Term) -> @kernel.Thm raise {
  @bool.ispec(ls, @drule.match_mp(thm("sl_triple_l_of"))(th))
}

///|
/// sl_triple_l(p2, bs, q2, ls) from `th` = sl_triple_l(p, bs, q, ls), by
/// sl_conseq_l: `ent` proves p2 ⇒ p and q ⇒ q2, with `hyps` (th's
/// hypotheses, which the result keeps) among the assumptions.
fn conseq_l(
  th : @kernel.Thm,
  p2 : @kernel.Term,
  q2 : @kernel.Term,
  ent : @tactics.Tactic,
  hyps? : Array[@kernel.Term] = [],
) -> @kernel.Thm raise {
  let (p, bs, q, ls) = triple_l_parts(th)
  let (head, _) = @basics.strip_comb(@kernel.concl(th))
  let mut goal = @basics.list_mk_comb(head, @list.List([p2, bs, q2, ls]))
  for k = hyps.length() - 1; k >= 0; k = k - 1 {
    goal = @bool.mk_imp(hyps[k], goal)
  }
  let mut result = @tactics.prove(
    goal,
    seq([
      @tactics.repeat_tac(@tactics.disch_tac),
      @tactics.match_mp_tac(thm("sl_conseq_l")),
      @tactics.exists_tac(p),
      @tactics.exists_tac(q),
      @tactics.exists_tac(ls),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([
        solve(@tactics.accept_tac(th)),
        solve(@simp.rewrite_tac(ths([]))),
        solve(seq([@tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))])),
        solve(ent),
      ])),
    ]),
  )
  for h in hyps {
    result = @bool.mp(result, @kernel.assume_rule(h))
  }
  result
}

///|
/// An entailment tactic: unfold st, take the premise apart, substitute,
/// rewrite with `rws` and the assumptions, and finish with MESON and `lemmas`.
fn ent_tac(
  rws? : Array[@kernel.Thm] = [],
  lemmas? : Array[@kernel.Thm] = [],
) -> @tactics.Tactic raise {
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([thm("st"), @lists.append(), @lists.append_nil()] + rws)),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @simp.asm_rewrite_tac(ths([@lists.append(), @lists.append_nil()] + rws)),
    @tactics.try_tac(@meson.asm_meson_tac(ths(lemmas))),
  ])
}

///|
/// (concl of th's antecedent, th with it discharged by `proof`).
fn discharge(th : @kernel.Thm, proof : (@kernel.Term) -> @kernel.Thm raise) -> @kernel.Thm raise {
  let ant = @kernel.rand(@kernel.rator(@kernel.concl(th)))
  @bool.mp(th, proof(ant))
}

///|
fn prove_example_sum() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let r = "(R : \{rty})"
  let nil = "(NIL : List[Value])"
  let n = "(n : \{w})"
  let acc = "(acc : \{w})"
  let n0 = "(n0 : \{w})"
  let acc0 = "(acc0 : \{w})"
  let vs0 = "(vs0 : List[Value])"
  let answer = "word_add(\{acc0}, word(sum_to(val(\{n0}))))"
  let n1 = "word_sub(\{n}, word(1))"
  let acc1 = "word_add(\{acc}, \{n})"
  let l0 = "[\{i(n)}, \{i(acc)}]"
  let l1 = "[\{i(n)}, \{i(acc1)}]"
  let l2 = "[\{i(n1)}, \{i(acc1)}]"
  let body_code = "[Local_get(1), Local_get(0), Binop(T_i32, Binop_i(Add)), Local_set(1), Local_get(0), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Sub)), Local_set(0), Local_get(0), Br_if(0)]"
  let linv = "(lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => ∃ n : \{w}, ∃ acc : \{w}, lc == [\{i("n")}, \{i("acc")}] && !(n == word(0)) && word_add(acc, word(sum_to(val(n)))) == \{answer} && \{r}(gs, h)"
  let done = "st(\{nil}, [\{i("word(0)")}, \{i(answer)}], \{r})"
  let no_br = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (h : \{heap}) => false"
  // the loop rule for this body: its premise names the label assertion
  let loop_rule = beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), tm(body_code), tm(linv), tm(done), tm("[\{no_br}]"), tm(nil)]),
      thm("sl_loop"),
    ),
  )
  let premise = @kernel.rand(@kernel.rator(@kernel.concl(loop_rule)))
  let (_, premise_args) = @basics.strip_comb(premise)
  let lb = premise_args.to_array()[0]
  let labels = premise_args.to_array()[3]
  // the straight-line part, from locals [n, acc]
  let steps = [
    inst("st_local_get", [nil, l0, r, "1"]),
    inst("st_local_get", ["[\{i(acc)}]", l0, r, "0"]),
    inst("st_binop", [nil, l0, r, "T_i32", "Binop_i(Add)", "ConstInt32(\{acc})", "ConstInt32(\{n})", "ConstInt32(\{acc1})"]),
    inst("st_local_set", [nil, l0, r, "1", "ConstInt32(\{acc1})"]),
    inst("st_local_get", [nil, l1, r, "0"]),
    inst("st_const", ["[\{i(n)}]", l1, r, "ConstInt32(word(1))"]),
    inst("st_binop", [nil, l1, r, "T_i32", "Binop_i(Sub)", "ConstInt32(\{n})", "ConstInt32(word(1))", "ConstInt32(\{n1})"]),
    inst("st_local_set", [nil, l1, r, "0", "ConstInt32(\{n1})"]),
    inst("st_local_get", [nil, l2, r, "0"]),
  ]
  let mut straight = steps[0]
  for k in 1..<steps.length() {
    straight = glue(straight, steps[k])
  }
  // br_if 0, under the invariant's facts about n and acc
  let facts = tm("!(\{n} == word(0)) && word_add(\{acc}, word(sum_to(val(\{n})))) == \{answer}")
  let step_inv = lemma(
    "sum_inv_step",
    "∀ n : \{w}, ∀ acc : \{w}, ∀ a : \{w}, !(n == word(0)) && word_add(acc, word(sum_to(val(n)))) == a → word_add(word_add(acc, n), word(sum_to(val(word_sub(n, word(1)))))) == a",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([@equal.gsym(@words.word_add_assoc())])),
      @simp.asm_simp_tac(ths([thm("sum_to_step")])),
    ]),
  )
  let br_rule = @bool.ispecl(@list.List([tm("0"), labels]), thm("sl_br"))
  let (br_pre, _, br_post, _) = triple_l_terms(@kernel.rand(@kernel.concl(br_rule)))
  let br_if = norm(
    @bool.ispecl(
      @list.List([tm("st(\{nil}, \{l2}, \{r})"), tm(done), labels, tm("0"), tm(n1)]),
      thm("sl_br_if"),
    ),
  )
  let br_if = discharge(br_if, ant => {
    let th = @tactics.prove(
      @bool.mk_imp(facts, ant),
      seq([
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            // n - 1 ≠ 0: br 0 back to the loop, with the invariant
            seq([
              @tactics.disch_tac,
              @tactics.match_mp_tac(thm("sl_conseq_l")),
              @tactics.exists_tac(br_pre),
              @tactics.exists_tac(br_post),
              @tactics.exists_tac(labels),
              @tactics.thenl(
                @tactics.repeat_tac(@tactics.conj_tac),
                @list.List([
                  // the state is the label's: n - 1 and acc + n keep the invariant
                  seq([
                    @tactics.repeat_tac(@tactics.gen_tac),
                    @simp.rewrite_tac(ths([thm("st")])),
                    @tactics.repeat_tac(@tactics.strip_tac),
                    subst_vars(),
                    @tactics.exists_tac(tm(nil)),
                    @tactics.exists_tac(tm(nil)),
                    @simp.rewrite_tac(ths([@lists.append(), @lists.el_cons()])),
                    @tactics.conv_tac(@calc_num.num_reduce_conv),
                    @simp.rewrite_tac(ths([])),
                    @meson.asm_meson_tac(ths([step_inv])),
                  ]),
                  seq([
                    @tactics.match_mp_tac(br_rule),
                    @simp.rewrite_tac(ths([@lists.length(), arith("∀ n : Num, 0 < SUC(n)")])),
                  ]),
                  @simp.rewrite_tac(ths([])),
                  @simp.rewrite_tac(ths([])),
                  seq([@tactics.repeat_tac(@tactics.strip_tac), @simp.asm_rewrite_tac(ths([]))]),
                ]),
              ),
            ]),
            // n - 1 = 0: out of the loop, with n = 1
            seq([
              @tactics.disch_tac,
              @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.word_sub_eq_0()]))),
              subst_vars(),
              @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("sum_to_one_word")]))),
              ent_tac(rws=[@words.word_sub_refl()]),
            ]),
          ]),
        ),
      ]),
    )
    @bool.mp(th, @bool.conj(
      @kernel.assume_rule(@kernel.rand(@kernel.rator(facts))),
      @kernel.assume_rule(@kernel.rand(facts)),
    ))
  })
  let body = glue(with_labels(straight, labels), br_if, rule="sl_seq_l")
  // the facts and n, acc come out of the precondition: it is the label
  let body = @tactics.prove(
    @bool.mk_imp(facts, @kernel.concl(body)),
    seq([@tactics.disch_then(th => @tactics.strip_assume_tac(th)), @tactics.accept_tac(body)]),
  )
  let body = beta(@drule.match_mp(thm("sl_pure_l"))(body))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(acc), body)))
  let body = beta(@drule.match_mp(thm("sl_ex_l"))(@bool.gen(tm(n), body)))
  let (_, _, body_post, _) = triple_l_parts(body)
  let body = conseq_l(body, lb, body_post, ent_tac())
  let looped = @bool.mp(loop_rule, body)
  // n0 ≠ 0: the block around the loop
  let (loop_pre, loop_code, loop_post, _) = triple_l_parts(looped)
  let start = tm("st(\{vs0}, [\{i(n0)}, \{i(acc0)}], \{r})")
  let finish = tm("st(\{vs0}, [\{i("word(0)")}, \{i(answer)}], \{r})")
  let block_rule = (code : @kernel.Term, pb : @kernel.Term, qb : @kernel.Term) => beta(
    @bool.ispecl(
      @list.List([tm("(NONE : Option[Valtype])"), code, pb, qb, tm(no_br), tm("(NIL : List[\{sassn}])"), tm(vs0)]),
      thm("sl_block"),
    ),
  )
  let nonzero = block_rule(loop_code, loop_pre, loop_post)
  let nonzero = @bool.mp(nonzero, looped)
  let nz = tm("!(\{n0} == word(0))")
  let nonzero = conseq_l(nonzero, start, finish, ent_tac(), hyps=[nz])
  // n0 = 0: the empty block
  let empty = tm("st(\{nil}, [\{i(n0)}, \{i(acc0)}], \{r})")
  let zero = block_rule(tm("(NIL : List[B_e])"), empty, empty)
  let zero = @bool.mp(zero, @bool.ispecl(@list.List([empty, tm("[\{no_br}]")]), thm("sl_nil_l")))
  let z = tm("\{n0} == word(0)")
  let zero = conseq_l(
    zero,
    start,
    finish,
    ent_tac(rws=[thm("sum_to_zero_word"), @words.word_add_0()]),
    hyps=[z],
  )
  // the if, and local.get 0 before it
  let if_rule = norm(
    @bool.ispecl(
      @list.List([
        start,
        finish,
        tm("(NIL : List[\{sassn}])"),
        tm("Tbv((NONE : Option[Valtype]))"),
        tm("[Loop(Tbv((NONE : Option[Valtype])), \{body_code})]"),
        tm("(NIL : List[B_e])"),
        tm(n0),
      ]),
      thm("sl_if"),
    ),
  )
  let if_rule = discharge(if_rule, ant => @tactics.prove(
    ant,
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        seq([@tactics.disch_tac, @tactics.accept_tac(nonzero)]),
        seq([@tactics.disch_tac, @tactics.accept_tac(zero)]),
      ]),
    ),
  ))
  let get = inst("st_local_get", [vs0, "[\{i(n0)}, \{i(acc0)}]", r, "0"])
  let all = glue(with_labels(get, tm("(NIL : List[\{sassn}])")), if_rule, rule="sl_seq_l")
  let all = @drule.match_mp(thm("sl_triple_of_l"))(all)
  record("example_sum", @bool.gen_all(all), kind="example")
}
