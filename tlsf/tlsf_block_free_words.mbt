// The six page metadata words become ordinary TLSF payload on reclamation.

///|
fn prove_tlsf_block_free_words() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let n = 6
  let ps = Array::makei(n, j => {
    "pts((a : Num)+\{4*j},serialise_i32((w\{j} : \{w32})))"
  })
  let own = small_star(ps + ["tlsf_bytes(a+24,(len : Num)-24)"])
  let ghosts = Array::makei(n, j => "∃ w\{j} : \{w32}, ").join("")
  let steps = Array::makei(n, j => {
    @simp.rewrite_rule(ths([@arith.add_clauses(), @arith.sub_0()]))(
      inst(thm("tlsf_page_allocate_word_prefix"), [
        "(a : Num)+\{4*j}",
        "(len : Num)-\{4*j}",
      ]),
    )
  })
  let _ = lemma(
    "tlsf_small_words6",
    "∀ a : Num, ∀ len : Num, 24 <= len → tlsf_bytes(a,len) == ((h : \{heap}) => \{ghosts}\{own}(h))",
    seq([
      gen,
      @tactics.disch_tac,
      seq(
        Array::makei(n, j => {
          free_have(
            if j == 0 {
              "4 <= (len : Num)"
            } else {
              "4 <= (len : Num)-\{4*j}"
            },
            @int.asm_arith_tac,
          )
        }),
      ),
      seq(
        steps.map(th => {
          seq([
            rw([
              @bool.mp(
                th,
                @kernel.assume_rule(@basics.dest_imp(@kernel.concl(th)).0),
              ),
            ]),
            rw([
              @arith.add_clauses(),
              arith("∀ a : Num, ∀ n : Num, ∀ m : Num, a+n+m == a+(n+m)"),
              arith("∀ a : Num, ∀ n : Num, ∀ m : Num, a-n-m == a-(n+m)"),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
          ])
        }),
      ),
      rw(
        [
          @arith.add_clauses(),
          arith("∀ a : Num, ∀ n : Num, ∀ m : Num, a+n+m == a+(n+m)"),
          arith("∀ a : Num, ∀ n : Num, ∀ m : Num, a-n-m == a-(n+m)"),
        ] +
        lift_rws(),
      ),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
}
