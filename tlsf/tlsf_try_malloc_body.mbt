///|
fn malloc_entry_variables() -> Array[(String, String)] {
  [
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("pop", "Num"),
    ("push", "Num"),
    ("initialize_idx", "Num"),
    ("page_idx", "Num"),
    ("take_idx", "Num"),
    ("ensure_idx", "Num"),
  ]
}

///|
fn prove_tlsf_try_malloc_body() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let model = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let params = page_arguments(model)
  let pre = "tlsf_try_malloc_pre(" + params + ")"
  let post = "tlsf_try_malloc_post(" + params + ")"
  let q = body_post(post)
  let zero = malloc_i("word(0)")
  let zeros = "[" + Array::make(4, zero).join(",") + "]"
  let lc = "[" + ([malloc_i(n)] + Array::make(4, zero)).join(",") + "]"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let p = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => val(" +
    n +
    ") <= 4160749568 && st(NIL," +
    lc +
    "," +
    r +
    ")(vs,lc,gs,ms,h)"
  let vs = [("G", malloc_g_variables()[0].1)] +
    malloc_entry_variables() +
    model +
    [("args", "List[Value]")]
  let focusargs = malloc_case_variables().map(x => {
    if ["l0", "l1", "l2", "l3", "l4"].contains(x.0) {
      zero
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let focus = @simp.pure_rewrite_rule(ths([thm("tlsf_malloc_try_body")]))(
    inst(thm("tlsf_malloc_try_attempt"), focusargs),
  )
  let _ = lemma(
    "tlsf_try_malloc_body",
    page_quantify(vs) +
    "(" +
    malloc_helper_natives() +
    ") → sl_triple_g((G : " +
    malloc_g_variables()[0].1 +
    "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    q +
    "," +
    body_pre(pre, "(args : List[Value])", zeros) +
    ",tlsf_try_malloc_code(" +
    a[0] +
    ",(initialize_idx : Num),(page_idx : Num),(take_idx : Num))," +
    q +
    ",[" +
    q +
    "])",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @simp.pure_rewrite_tac(ths([thm("tlsf_try_malloc_code")])),
        @logic.match_mp_tac(thm("sl_conseq_g")),
        @tactics.exists_tac(tm(p)),
        @tactics.exists_tac(tm(q)),
        @tactics.exists_tac(tm("[" + q + "]")),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              ent_tac(
                [
                  thm("tlsf_try_malloc_pre"),
                  thm("tlsf_malloc_ro"),
                  @lists.append(),
                ],
                [],
              ),
            ),
            solve(
              seq([
                @logic.match_mp_tac(thm("sl_pure_g")),
                @tactics.disch_tac,
                free_apply(focus),
              ]),
            ),
            solve(same_tac()),
          ]),
        ),
      ])
    },
  )
}
