// The guard's initialization call uses the compiled native initializer, with
// its original-heap abort postcondition, rather than an assumed helper spec.

///|
fn malloc_start_push_native() -> String {
  "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native((inst : Inst),Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : " +
  w32 +
  ")))"
}

///|
fn prove_tlsf_malloc_start_initialize() -> Unit raise {
  let vars = malloc_entry_variables() +
    [
      ("d", w32),
      ("lim", "Num"),
      ("before", heap),
      ("fp", rty),
      ("lc", "List[Value]"),
    ]
  let env = startup_env()
  let r = malloc_start_saved()
  let post = malloc_start_initialized()
  let ap = "tlsf_initialize_abort((d : " +
    w32 +
    "),(lim : Num),(before : " +
    heap +
    "),(fp : " +
    rty +
    "))"
  let lc = "(lc : List[Value])"
  let cond = "tlsf_initialize_valid((d : " +
    w32 +
    "),(lim : Num)) && " +
    malloc_start_initialize_native() +
    " && " +
    malloc_start_push_native()
  let initialize = inst(thm("tlsf_initialize_all"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : " + w32 + ")",
    "(initialize_idx : Num)",
    "(push : Num)",
    "(lim : Num)",
    "(before : " + heap + ")",
    "(fp : " + rty + ")",
    lc,
  ])
  let call = startup_lemma(
    "tlsf_malloc_start_initialize_call",
    page_quantify(vars) +
    cond +
    " → sl_abort_m(" +
    env +
    ",st(NIL," +
    lc +
    "," +
    r +
    "),[Call(initialize_idx)],st(NIL," +
    lc +
    "," +
    post +
    ")," +
    ap +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      initialize_abort_conseq(
        initialize,
        ent_tac([thm("tlsf_initialize_pre"), thm("tlsf_initialize_saved")], []),
        same_tac(),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_malloc_start_initialize_if",
    page_quantify(vars) +
    cond +
    " → sl_abort_m(" +
    env +
    ",st([" +
    malloc_i("word(1)") +
    "]," +
    lc +
    "," +
    r +
    "),tlsf_malloc_start_guard_call(" +
    page_arguments(malloc_env_variables()) +
    "),st(NIL," +
    lc +
    "," +
    post +
    ")," +
    ap +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @logic.abort_sym_tac([call], startup_vc()),
    ]),
  )
  let params = malloc_entry_variables() +
    [
      ("d", w32),
      ("lim", "Num"),
      ("before", heap),
      ("fp", rty),
      ("l0", "Value"),
      ("l1", "Value"),
      ("rest", "List[Value]"),
    ]
  let slot = "word_add(word_and(word_add((d : " +
    w32 +
    "),word(15)),word(4294967280)),word(1908))"
  let initial = "CONS((l0 : Value),CONS((l1 : Value),(rest : List[Value])))"
  let ready = "CONS((l0 : Value),CONS(" +
    malloc_i(slot) +
    ",(rest : List[Value])))"
  let raw = inst(
    thm("tlsf_malloc_start_guard_test_raw"),
    malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")") +
    [
      "(lim : Num)",
      "(before : " + heap + ")",
      "(fp : " + rty + ")",
      "(l0 : Value)",
      "(l1 : Value)",
      "(rest : List[Value])",
    ],
  )
  let after_call = inst(
    thm("tlsf_malloc_start_initialize_if"),
    malloc_entry_variables().map(x => "(" + x.0 + " : " + x.1 + ")") +
    [
      "(d : " + w32 + ")",
      "(lim : Num)",
      "(before : " + heap + ")",
      "(fp : " + rty + ")",
      ready,
    ],
  )
  let _ = startup_lemma(
    "tlsf_malloc_start_ready",
    page_quantify(params) +
    cond +
    " → sl_abort_m(" +
    env +
    ",st(NIL," +
    initial +
    "," +
    r +
    ")," +
    malloc_part("try", "ready_guard") +
    ",st(NIL," +
    ready +
    "," +
    post +
    ")," +
    ap +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @logic.abort_sym_tac([raw, after_call], startup_vc()),
    ]),
  )
}
