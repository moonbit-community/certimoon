///|
fn malloc_full_natives() -> String raise {
  malloc_helper_natives() +
  " && EL(sfunc_ind((inst : Inst),(ensure_idx : Num)),(fs : List[Cl])) == Func_native((inst : Inst),Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32)],tlsf_ensure_code((d : " +
  w32 +
  "),(pop : Num),(push : Num)))"
}

///|
fn malloc_abort_post(a : Array[String]) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => tlsf_malloc_state(" +
  a[0] +
  "," +
  a[1] +
  ",(fp : " +
  rty +
  "))(gs,ms,h)"
}

///|
fn malloc_growth_post(a : Array[String], lc : String) -> String {
  let newer = malloc_fresh_args(a)
  newer[1] = "(lim2 : Num)"
  let choices = [("lim2", "Num"), ("before2", heap)] +
    page_model_variables()[2:8].to_owned().map(x => (x.0 + "2", x.1))
  let frame = "(gs : List[Value]) => (ms : Num) => (fp : " +
    rty +
    ")(gs," +
    a[1] +
    ")"
  let r = "tlsf_malloc_ro(" +
    (newer + ["(before2 : " + heap + ")", frame]).join(",") +
    ")"
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => " +
  choices.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("") +
  a[1] +
  " <= (lim2 : Num) && st(NIL," +
  lc +
  "," +
  r +
  ")(vs,lc,gs,ms,h)"
}

///|
fn prove_tlsf_malloc_full_growth() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let vars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let env = [
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("pop", "Num"),
    ("push", "Num"),
    ("ensure_idx", "Num"),
  ]
  let ensure = inst(
    thm("tlsf_malloc_ensure_call"),
    env.map(x => "(" + x.0 + " : " + x.1 + ")") +
    a +
    [
      "(request : " + w32 + ")",
      "(before : " + heap + ")",
      "(fp : " + rty + ")",
      "(caller : List[Value])",
    ],
  )
  let choices = ["(lim2 : Num)", "(before2 : " + heap + ")"] +
    malloc_fresh_args(a)[2:8].to_owned()
  let normal = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
    @tactics.repeat_tac(@tactics.strip_tac),
    seq(choices.map(x => @tactics.exists_tac(tm(x)))),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let vc = @tactics.first(
    @list.List([solve(malloc_abort_vc(a)), solve(normal)]),
  )
  let cond = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && 0 < val(" +
    n +
    ") && val(" +
    n +
    ") <= 4160749568 && (" +
    malloc_full_natives() +
    ")"
  let code = "tlsf_malloc_full_growth(" +
    page_arguments(malloc_env_variables()) +
    ")"
  let _ = lemma(
    "tlsf_malloc_full_growth_all",
    page_quantify(vars) +
    cond +
    " → sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    malloc_growth_post(a, lc) +
    "," +
    malloc_abort_post(a) +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @logic.abort_sym_tac([ensure], vc),
    ]),
  )
}
