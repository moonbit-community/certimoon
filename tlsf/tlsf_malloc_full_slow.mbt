///|
fn prove_tlsf_full_malloc_slow_body(tail_only~ : Bool = false) -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let fp = "(fp : " + rty + ")"
  let before = "(before : " + heap + ")"
  let r = "tlsf_malloc_ro(" + (a + [before, fp]).join(",") + ")"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let model = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let q = body_post("tlsf_full_malloc_post(" + page_arguments(model) + ")")
  let vars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let args = vars.map(x => "(" + x.0 + " : " + x.1 + ")")
  let source = inst(thm("tlsf_malloc_slow_prefix"), args)
  let growth = inst(thm("tlsf_malloc_full_growth_all"), args)
  let newer = malloc_fresh_args(a)
  newer[1] = "(lim2 : Num)"
  let frame = "(gs : List[Value]) => (ms : Num) => (" +
    fp +
    ")(gs," +
    a[1] +
    ")"
  let retryargs = vars.map(x => {
    if x.0 == "before" {
      "(before2 : " + heap + ")"
    } else if x.0 == "fp" {
      frame
    } else if page_model_variables().any(y => y.0 == x.0) {
      newer[page_model_variables().map(y => y.0).search(x.0).unwrap()]
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let retry = @simp.pure_rewrite_rule(ths([thm("tlsf_malloc_checked_post")]))(
    inst(thm("tlsf_malloc_retry_checked"), retryargs),
  )
  let cond = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && 0 < val(" +
    n +
    ") && val(" +
    n +
    ") <= 4160749568 && !" +
    malloc_available(a, n) +
    " && (" +
    malloc_full_natives() +
    ")"
  let code = (if tail_only {
      "tlsf_malloc_start_full_tail("
    } else {
      "tlsf_full_malloc_code("
    }) +
    page_arguments(malloc_env_variables()) +
    ")"
  let _ = lemma(
    if tail_only {
      "tlsf_full_malloc_slow_tail"
    } else {
      "tlsf_full_malloc_slow_body"
    },
    page_quantify(vars) +
    cond +
    " → sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    (if tail_only {
      malloc_slow_prefix_post(a, n)
    } else {
      "st(NIL," + lc + "," + r + ")"
    }) +
    "," +
    code +
    "," +
    q +
    "," +
    malloc_abort_post(a) +
    ")",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @logic.abort_sym_tac(
          (if tail_only { [] } else { [source] }) +
          [thm("tlsf_malloc_early_failure"), growth, retry],
          malloc_abort_vc(a),
        ),
      ])
    },
  )
}
