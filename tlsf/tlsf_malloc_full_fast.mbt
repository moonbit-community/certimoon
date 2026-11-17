///|
fn define_tlsf_full_malloc_fast_pre() -> Unit raise {
  let vars = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let params = page_arguments(vars)
  def(
    "tlsf_full_malloc_fast_pre",
    "tlsf_full_malloc_fast_pre(" +
    params +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => " +
    malloc_available(block_model_args(), "(n : " + w32 + ")") +
    " && tlsf_try_malloc_pre(" +
    params +
    ")(res,gs,ms,h))",
  )
}

///|
fn malloc_fast_prefix_post(a : Array[String], n : String) -> String {
  let post = "tlsf_full_malloc_post(" +
    (a + [n, "(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let work = ["out0", "out1", "out2", "out3", "out4"]
  let lc = "[" +
    ([malloc_i(n)] + work.map(x => "(" + x + " : Value)")).join(",") +
    "]"
  "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => " +
  work.map(x => "∃ " + x + " : Value, ").join("") +
  "lc == " +
  lc +
  " && (∃ ptr : " +
  w32 +
  ", res == [" +
  malloc_i("(ptr : " + w32 + ")") +
  "] && !(ptr == word(4294967295)) && " +
  post +
  "(res,gs,ms,h))"
}

///|
fn prove_tlsf_malloc_fast_prefix() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let vars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let source = inst(
    thm("tlsf_malloc_first_block"),
    vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
  )
  let code = "tlsf_malloc_full_prefix(" +
    page_arguments(malloc_env_variables()) +
    ")"
  let post = malloc_fast_prefix_post(a, n)
  let cond = "val(" +
    n +
    ") <= 4160749568 && (" +
    malloc_helper_natives() +
    ") && " +
    malloc_available(a, n)
  let closed = lemma(
    "tlsf_malloc_fast_prefix",
    page_quantify(vars) +
    cond +
    " → sl_triple_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    post +
    ",NIL)",
    () => {
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
            subst_vars(),
            seq(
              ["out0", "out1", "out2", "out3", "out4"].map(x => {
                @tactics.exists_tac(tm("(" + x + " : Value)"))
              }),
            ),
            @simp.asm_rewrite_tac(ths([])),
            free_apply(
              inst(
                thm("tlsf_malloc_try_available"),
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
      ])
    },
  )
  let _ = lemma(
    "tlsf_malloc_fast_prefix_g",
    page_quantify(malloc_case_variables()) +
    cond +
    " → sl_triple_g(" +
    malloc_g_env() +
    ",st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    post +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_lift(inst(closed, vars.map(x => "(" + x.0 + " : " + x.1 + ")"))),
      ])
    },
  )
}

///|
fn prove_tlsf_full_malloc_fast_body() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let vars = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let params = page_arguments(vars)
  let pre = "tlsf_full_malloc_fast_pre(" + params + ")"
  let q = body_post("tlsf_full_malloc_post(" + params + ")")
  let prefix = malloc_fast_prefix_post(a, n)
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let code = "tlsf_full_malloc_code(" +
    page_arguments(malloc_env_variables()) +
    ")"
  let first = @basics.dest_list(
      malloc_program_code(
        "tlsf_malloc_full_prefix(" +
        page_arguments(malloc_env_variables()) +
        ")",
      ),
    )
    .head()
    .unwrap()
  let afters = malloc_continuations(malloc_program_code(code)).map(x => {
    if x == first {
      prefix
    } else {
      malloc_false()
    }
  })
  let args = malloc_case_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
  let cond = "val(" +
    n +
    ") <= 4160749568 && (" +
    malloc_helper_natives() +
    ") && " +
    malloc_available(a, n)
  let focus = sym_prove(
    "tlsf_full_malloc_fast_focused",
    page_quantify(malloc_case_variables()) +
    cond +
    " → sl_triple_g((G : " +
    malloc_g_variables()[0].1 +
    "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    q +
    ",st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    q +
    ",[" +
    q +
    "])",
    [],
    () => Array::make(15, malloc_vc(extra=[thm("tlsf_full_malloc_post")])),
    afters~,
    chunks=[inst(thm("tlsf_malloc_fast_prefix_g"), args)],
    rws=[thm("tlsf_full_malloc_post")] + malloc_extra_rewrites(),
    kind="lemma",
  )
  let zero = malloc_i("word(0)")
  let zeros = "[" + Array::make(5, zero).join(",") + "]"
  let focusargs = malloc_case_variables().map(x => {
    if ["l0", "l1", "l2", "l3", "l4"].contains(x.0) {
      zero
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let focus = inst(focus, focusargs)
  let p = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (val(" +
    n +
    ") <= 4160749568 && " +
    malloc_available(a, n) +
    ") && st(NIL," +
    lc
    .replace(old="(l0 : Value)", new=zero)
    .replace(old="(l1 : Value)", new=zero)
    .replace(old="(l2 : Value)", new=zero)
    .replace(old="(l3 : Value)", new=zero)
    .replace(old="(l4 : Value)", new=zero) +
    "," +
    r +
    ")(vs,lc,gs,ms,h)"
  let allvars = [("G", malloc_g_variables()[0].1)] +
    malloc_entry_variables() +
    vars +
    [("args", "List[Value]")]
  let _ = lemma(
    "tlsf_full_malloc_fast_body",
    page_quantify(allvars) +
    "(" +
    malloc_helper_natives() +
    ") → sl_triple_g((G : " +
    malloc_g_variables()[0].1 +
    "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    q +
    "," +
    body_pre(pre, "(args : List[Value])", zeros) +
    "," +
    code +
    "," +
    q +
    ",[" +
    q +
    "])",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
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
                  thm("tlsf_full_malloc_fast_pre"),
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
                @tactics.repeat_tac(@tactics.strip_tac),
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

///|
fn prove_tlsf_full_malloc_fast_module() -> Unit raise {
  malloc_close_entry("full_fast", 5)
}
