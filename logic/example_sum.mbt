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
// sum_to(n) the answer. sym_prove runs the code; what is left is the
// arithmetic: the invariant again (sum_inv_step), the exit with n - 1 = 0
// (n is 1), and the empty branch with n0 = 0.

///|
fn prove_example_sum() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let answer = "word_add(acc0, word(sum_to(val(n0))))"
  let body = "[Local_get(1), Local_get(0), Binop(T_i32, Binop_i(Add)), Local_set(1), Local_get(0), EConstNum(ConstInt32(word(1))), Binop(T_i32, Binop_i(Sub)), Local_set(0), Local_get(0), Br_if(0)]"
  let code = "[Local_get(0), If(Tbv(NONE), [Loop(Tbv(NONE), \{body})], NIL)]"
  let inv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ n : \{w}, ∃ acc : \{w}, lc == [\{i("n")}, \{i("acc")}] && !(n == word(0)) && word_add(acc, word(sum_to(val(n)))) == word_add((acc0 : \{w}), word(sum_to(val((n0 : \{w}))))) && (R : \{rty})(gs, ms, h)"
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
  let _ = sym_prove(
    "example_sum",
    "∀ vs0 : List[Value], ∀ acc0 : \{w}, ∀ n0 : \{w}, ∀ R : \{rty}, sl_triple(st(vs0, [\{i("n0")}, \{i("acc0")}], R), \{code}, st(vs0, [\{i("word(0)")}, \{i(answer)}], R))",
    [inv],
    [
      // the invariant again
      seq([@tactics.match_mp_tac(step_inv), @simp.asm_rewrite_tac(ths([]))]),
      // out of the loop: n - 1 = 0, so n is 1
      seq([
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@words.word_sub_eq_0()]))),
        subst_vars(),
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("sum_to_one_word")]))),
        @simp.asm_rewrite_tac(ths([])),
      ]),
      // n0 = 0
      @simp.rewrite_tac(ths([thm("sum_to_zero_word"), @words.word_add_0()])),
    ],
  )
}

///|
/// The parts (p, bs, q, ls) of the term `sl_triple_l(p, bs, q, ls)`.
fn triple_l_terms(
  t : @kernel.Term,
) -> (@kernel.Term, @kernel.Term, @kernel.Term, @kernel.Term) raise {
  let (_, args) = @basics.strip_comb(t)
  guard args.to_array() is [p, bs, q, ls] else {
    raise Failure("wasmcert/logic: not a triple with labels: " + show(t))
  }
  (p, bs, q, ls)
}
