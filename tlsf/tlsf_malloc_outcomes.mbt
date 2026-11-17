// Classify complete attempts, then transport their client frame through growth.

///|
fn prove_tlsf_malloc_outcomes() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let fp = "(fp : " + rty + ")"
  let model = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let vars = model +
    [("res", "List[Value]"), ("gs", "List[Value]"), ("ms", "Num"), ("h", heap)]
  let params = page_arguments(model)
  let post = "tlsf_try_malloc_post(" +
    params +
    ")((res : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))"
  let full = "tlsf_full_malloc_post(" +
    params +
    ")((res : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_malloc_try_available",
    page_quantify(vars) +
    malloc_available(a, n) +
    " && " +
    post +
    " → (∃ ptr : " +
    w32 +
    ", res == [" +
    malloc_i("(ptr : " + w32 + ")") +
    "] && !(ptr == word(4294967295)) && " +
    full +
    ")",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(ths([thm("tlsf_try_malloc_post")])),
        strip,
        subst_vars(),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.exists_tac(tm("(word(0) : " + w32 + ")")),
                arw([
                  thm("tlsf_full_malloc_post"),
                  @equal.gsym(@words.val_eq()),
                  @words.val_word(),
                  @words.dimindex_32(),
                ]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
                @simp.asm_rewrite_tac(ths([])),
              ]),
            ),
            solve(page_publish_atomic([])),
            solve(
              seq([
                @tactics.first_assum(th => {
                  if head_name(@kernel.concl(th)) == "tlsf_malloc_result" {
                    @tactics.strip_assume_tac(
                      @drule.match_mp(
                        @bool.spec_all(thm("tlsf_malloc_result_pointer")),
                      )(th),
                    )
                  } else {
                    @tactics.no_tac
                  }
                }),
                @tactics.exists_tac(tm("(ptr : " + w32 + ")")),
                arw([thm("tlsf_full_malloc_post")]),
                @tactics.try_tac(page_publish_atomic([])),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let unchanged = "ms == " +
    a[1] +
    " && h == (before : " +
    heap +
    ") && star(tlsf_allocator(" +
    a.join(",") +
    "),(" +
    fp +
    ")(gs," +
    a[1] +
    "),h)"
  let _ = lemma(
    "tlsf_malloc_try_no_fit",
    page_quantify(vars) +
    "!" +
    malloc_available(a, n) +
    " && " +
    post +
    " → !(" +
    n +
    " == word(0)) && res == [" +
    malloc_i("word(4294967295)") +
    "] && " +
    unchanged,
    () => {
      seq([
        gen,
        @simp.rewrite_tac(ths([thm("tlsf_try_malloc_post")])),
        strip,
        subst_vars(),
        arw([]),
        page_publish_atomic([]),
      ])
    },
  )
  let old = "(oldlim : Num)"
  let _ = lemma(
    "tlsf_malloc_frame_state",
    page_quantify(
      page_model_variables() +
      [
        ("oldlim", "Num"),
        ("fp", rty),
        ("gs", "List[Value]"),
        ("ms", "Num"),
        ("h", heap),
      ],
    ) +
    old +
    " <= " +
    a[1] +
    " && ms == " +
    a[1] +
    " && star(tlsf_allocator(" +
    a.join(",") +
    "),(" +
    fp +
    ")(gs," +
    old +
    "),h) → tlsf_malloc_state(" +
    a[0] +
    "," +
    old +
    "," +
    fp +
    ")(gs,ms,h)",
    () => {
      seq([
        gen,
        strip,
        @simp.rewrite_tac(ths([thm("tlsf_malloc_state")])),
        arw([]),
        seq(a[2:].to_owned().map(x => @tactics.exists_tac(tm(x)))),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_malloc_result_full_post",
    page_quantify(vars + [("ptr", w32)]) +
    "!(" +
    n +
    " == word(0)) && res == [" +
    malloc_i("(ptr : " + w32 + ")") +
    "] && tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    a[1] +
    "," +
    fp +
    ",(ptr : " +
    w32 +
    "))(gs,ms,h) → " +
    full,
    () => {
      seq([
        gen,
        strip,
        @simp.rewrite_tac(ths([thm("tlsf_full_malloc_post")])),
        arw([]),
        @tactics.exists_tac(tm("(ptr : " + w32 + ")")),
        arw([]),
      ])
    },
  )
}
