///|
fn define_tlsf_malloc_checked_post() -> Unit raise {
  let a = block_model_args()
  let vars = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let n = "(n : " + w32 + ")"
  let same = "(ms : Num) == " +
    a[1] +
    " && (h : " +
    heap +
    ") == (before : " +
    heap +
    ") && star(tlsf_allocator(" +
    a.join(",") +
    "),(fp : " +
    rty +
    ")(gs," +
    a[1] +
    "),h)"
  let zero = n +
    " == word(0) && res == [" +
    malloc_i("word(0)") +
    "] && (" +
    same +
    ")"
  let failure = "res == [" +
    malloc_i("word(4294967295)") +
    "] && (" +
    same +
    ")"
  let success = "∃ ptr : " +
    w32 +
    ", !(" +
    n +
    " == word(0)) && res == [" +
    malloc_i("(ptr : " + w32 + ")") +
    "] && !(ptr == word(4294967295)) && tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    a[1] +
    ",(fp : " +
    rty +
    "),(ptr : " +
    w32 +
    "))(gs,ms,h)"
  def(
    "tlsf_malloc_checked_post",
    "tlsf_malloc_checked_post(" +
    page_arguments(vars) +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (" +
    zero +
    ") || (" +
    failure +
    ") || (" +
    success +
    "))",
  )
}

///|
fn prove_tlsf_malloc_checked_post() -> Unit raise {
  let _a = block_model_args()
  let vars = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let params = page_arguments(vars)
  let state = "((res : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))"
  let _ = lemma(
    "tlsf_malloc_try_checked",
    page_quantify(
      vars +
      [
        ("res", "List[Value]"),
        ("gs", "List[Value]"),
        ("ms", "Num"),
        ("h", heap),
      ],
    ) +
    "tlsf_try_malloc_post(" +
    params +
    ")" +
    state +
    " → tlsf_malloc_checked_post(" +
    params +
    ")" +
    state,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(
        ths([thm("tlsf_try_malloc_post"), thm("tlsf_malloc_checked_post")]),
      ),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      @tactics.first(
        @list.List([
          solve(@simp.asm_rewrite_tac(ths([]))),
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
              @simp.asm_rewrite_tac(ths([])),
              @tactics.repeat_tac(@tactics.disj2_tac),
              @tactics.try_tac(@tactics.exists_tac(tm("(ptr : " + w32 + ")"))),
              @simp.asm_rewrite_tac(ths([])),
              page_publish_atomic([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}

///|
fn prove_tlsf_malloc_retry_checked() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let vars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let source = inst(
    thm("tlsf_malloc_retry_block"),
    vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
  )
  let t = args_of(@basics.dest_imp(@kernel.concl(source)).1, "sl_triple_m", 7).unwrap()
  let post = malloc_attempt_post("retry", a, n).replace(
    old="tlsf_try_malloc_post",
    new="tlsf_malloc_checked_post",
  )
  let need = show(@basics.dest_imp(@kernel.concl(source)).0)
  let _ = lemma(
    "tlsf_malloc_retry_checked",
    page_quantify(vars) +
    need +
    " → sl_triple_m(" +
    page_arguments(malloc_g_variables()[1:4].to_owned()) +
    "," +
    show(t[3]) +
    "," +
    show(t[4]) +
    "," +
    post +
    ",NIL)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      initialize_m_conseq(
        source,
        same_tac(),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          beta_goal(),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          seq(
            ["out0", "out1", "out2", "out3", "out4"].map(x => {
              @tactics.exists_tac(tm("(" + x + " : Value)"))
            }),
          ),
          @simp.asm_rewrite_tac(ths([])),
          free_apply(
            inst(
              thm("tlsf_malloc_try_checked"),
              a +
              [
                n,
                "(before : " + heap + ")",
                "(fp : " + rty + ")",
                "(vs : List[Value])",
                "(gs : List[Value])",
                "(ms : Num)",
                "(h : " + heap + ")",
              ],
            ),
          ),
        ]),
      ),
    ]),
  )
}
