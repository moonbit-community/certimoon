// The compiled loop walks the slots in ascending order and prepends each to
// the local free list. Its invariant owns only the new page and a frame.

///|
fn prove_tlsf_page_allocate_loop() -> Unit raise {
  let w = w32
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let total = "tlsf_small_total(val(\{s}))"
  let k = "(k : Num)"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let head = (n : String) => "tlsf_page_allocate_head(\{p},val(\{s}),\{n})"
  let slot = "tlsf_small_slot(\{p},val(\{s}),\{k})"
  let build = (n : String) => {
    "tlsf_page_allocate_build(\{p},(cap : Num),val(\{s}),\{n},(used0 : \{w}),(prev0 : \{w}))"
  }
  let own = (n : String) => {
    small_star([build(n), "(fp : " + rty + ")((gs : List[Value]),(ms : Num))"]) +
    "((h : " +
    heap +
    "))"
  }
  let lc = (n : String, l4 : String) => {
    "[\{i(s)},\{i(p)},\{i(head(n))},\{i("word("+n+")")},\{l4},\{i("word("+total+")")}]"
  }
  let lambda = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => "
  let inv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ k : Num, ∃ scratch : Value, 1 <= k && k <= \{total} && lc == \{lc(k,"scratch")} && \{own(k)}"
  let pre = lambda +
    "∃ k : Num, ∃ scratch : Value, 1 <= k && k <= \{total} && vs == NIL && lc == \{lc(k,"scratch")} && \{own(k)}"
  let done = lambda +
    "∃ scratch : Value, vs == NIL && lc == \{lc(total,"scratch")} && \{own(total)}"
  let next = lambda +
    "∃ k : Num, 1 <= k && k < \{total} && vs == [\{i("word(SUC(k))")}] && lc == [\{i(s)},\{i(p)},\{i(slot)},\{i("word(k)")},\{i(slot)},\{i("word("+total+")")}] && \{own("SUC(k)")}"
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ used0 : \{w}, ∀ prev0 : \{w}, ∀ fp : \{rty}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let start = seq([gen, beta_goal(), @tactics.try_tac(strip)])
  let capacity = free_have(
    "4 <= \{total} && \{total} <= 66",
    seq([
      @tactics.undisch_tac(
        tm("tlsf_page_allocate_geometry(\{p},(cap : Num),val(\{s}))"),
      ),
      rw([thm("tlsf_page_allocate_geometry")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_small_capacity"), ["val(" + s + ")"])),
      arw([]),
      small_meson(ths([])),
    ]),
  )
  let compare = (j : String) => {
    seq([
      capacity,
      free_have(
        "word_ult((word(\{j}) : \{w}),word(\{total})) == (\{j} < \{total})",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_page_allocate_compare"), [j, total]),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([
            @kernel.assume_rule(
              tm(
                "word_ult((word(" +
                j +
                ") : " +
                w +
                "),word(" +
                total +
                ")) == (" +
                j +
                " < " +
                total +
                ")",
              ),
            ),
          ]),
        ),
      ),
    ])
  }
  let vcs = [
    seq([start, @tactics.exists_tac(tm("(k : Num)")), arw([])]),
    seq([start, compare("(k' : Num)"), arw([]), @int.asm_arith_tac]),
    seq([
      start,
      compare("(k' : Num)"),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.exists_tac(tm("[" + i("word(SUC((k' : Num)))") + "]")),
      rw([@lists.append(), @lists.length()]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @tactics.exists_tac(tm("(k' : Num)")),
      arw([]),
    ]),
    seq([
      start,
      compare("(k' : Num)"),
      free_have("(k' : Num) == \{total}", @int.asm_arith_tac),
      subst_vars(),
      arw([]),
    ]),
    seq([
      start,
      g => {
        let ex = @logic.prove(
          tm("∃ vs : List[Value], (NIL : List[Value]) == vs"),
          seq([@tactics.exists_tac(tm("(NIL : List[Value])")), rw([])]),
        )
        @tactics.accept_tac(@kernel.eq_mp(norm_conv()(@kernel.concl(ex)), ex))(
          g,
        )
      },
    ]),
    seq([
      start,
      @tactics.exists_tac(tm("SUC((k'' : Num))")),
      arw([thm("tlsf_page_allocate_head_suc")]),
      @int.asm_arith_tac,
    ]),
  ]

  ignore(
    sym_prove(
      "tlsf_page_allocate_loop_build",
      "\{vars}, tlsf_page_allocate_geometry(\{p},cap,val(\{s})) → sl_triple(\{pre},tlsf_page_allocate_loop(take_idx),\{done})",
      [inv],
      () => vcs,
      afters=[next, done],
      chunks=[thm("tlsf_page_allocate_step_build")],
      kind="lemma",
    ),
  )
}
