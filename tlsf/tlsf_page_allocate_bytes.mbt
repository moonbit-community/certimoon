// Split arbitrary recycled payloads into writable words without zeroing or
// imposing a value on any byte the initialization code does not write.

///|
fn prove_tlsf_page_allocate_bytes() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_allocate_word_prefix",
    "∀ a : Num, ∀ n : Num, 4 <= n → tlsf_bytes(a,n) == ((h : \{heap}) => ∃ v : \{w32}, star(pts(a,serialise_i32(v)),tlsf_bytes(a+4,n-4),h))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have("4+((n : Num)-4) == n", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("tlsf_bytes_split"), ["(a : Num)", "4", "(n : Num)-4"]),
        ),
        arw([thm("tlsf_bytes_word")] + lift_rws()),
      ])
    },
  )
  let words = (n : Int32) => {
    let ps = Array::makei(n, j => {
      "pts((a : Num)+\{4*j},serialise_i32((w\{j} : \{w32})))"
    })
    let own = small_star(ps + ["tlsf_bytes(a+\{4*n},(len : Num)-\{4*n})"])
    let ghosts = Array::makei(n, j => "∃ w\{j} : \{w32}, ").join("")
    let steps = Array::makei(n, j => {
      @simp.rewrite_rule(ths([@arith.add_clauses(), @arith.sub_0()]))(
        inst(thm("tlsf_page_allocate_word_prefix"), [
          "(a : Num)+\{4*j}",
          "(len : Num)-\{4*j}",
        ]),
      )
    })
    lemma(
      "tlsf_page_allocate_words\{n}",
      "∀ a : Num, ∀ len : Num, \{4*n} <= len → tlsf_bytes(a,len) == ((h : \{heap}) => \{ghosts}\{own}(h))",
      () => {
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
                  arith(
                    "∀ a : Num, ∀ n : Num, ∀ m : Num, a+n+m == a+(n+m)",
                  ),
                  arith(
                    "∀ a : Num, ∀ n : Num, ∀ m : Num, a-n-m == a-(n+m)",
                  ),
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
        ])
      },
    )
  }
  ignore(words(3))
  ignore(words(9))
}

///|
fn prove_tlsf_page_allocate_one() -> Unit raise {
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_allocate_istar_one",
    "∀ f : (Num) -> \{hprop}, tlsf_istar(f,1) == f(0)",
    () => {
      seq([rw([arith("1 == SUC(0)"), thm("tlsf_istar"), thm("star_emp_hl")])])
    },
  )
  let _ = lemma(
    "tlsf_page_allocate_slot_zero",
    "∀ p : \{w32}, ∀ s : Num, tlsf_small_slot(p,s,0) == word_add(p,word(32))",
    () => {
      seq([
        rw([
          thm("tlsf_small_slot"),
          @arith.mult_clauses(),
          @arith.add_clauses(),
          @words.word_add_v1(),
          @words.word_val(),
          @words.word_add_0(),
        ]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_page_allocate_head_one",
    "∀ p : \{w32}, ∀ s : Num, tlsf_page_allocate_head(p,s,1) == word_add(p,word(32))",
    () => {
      seq([
        rw([thm("tlsf_page_allocate_head")]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        rw([thm("tlsf_page_allocate_slot_zero")]),
      ])
    },
  )
}
