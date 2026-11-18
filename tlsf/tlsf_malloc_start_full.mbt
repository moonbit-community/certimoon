// Close the first result block before composing the full allocator's tail.

///|
fn malloc_start_full_post() -> String {
  body_post(
    "tlsf_full_malloc_start_post((d : \{w32}),(n : \{w32}),(lim : Num),(before : \{heap}),(fp : \{rty}))",
  )
}

///|
fn malloc_start_abort() -> String {
  "tlsf_malloc_start_abort((d : \{w32}),(lim : Num),(before : \{heap}),(fp : \{rty}))"
}

///|
fn prove_tlsf_malloc_start_full() -> Unit raise {
  let vars = malloc_start_vars() +
    [
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  let n = "(n : \{w32})"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let p = "st(NIL," + lc + "," + malloc_start_saved() + ")"
  let q = malloc_start_attempt_post("first")
  let args = vars.map(x => "(" + x.0 + " : " + x.1 + ")")
  let arityvars = malloc_start_vars() +
    [
      ("vs", "List[Value]"),
      ("lc", "List[Value]"),
      ("gs", "List[Value]"),
      ("ms", "Num"),
      ("h", heap),
    ]
  let arity = startup_lemma(
    "tlsf_malloc_start_first_label",
    page_quantify(arityvars) +
    "(LENGTH((vs : List[Value])) == 1 && (" +
    q +
    ")(vs,lc,gs,ms,h)) == (" +
    q +
    ")(vs,lc,gs,ms,h)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      beta_goal(),
      startup_meson(ths([thm("tlsf_try_malloc_post_arity")])),
    ]),
  )
  let first = inst(thm("tlsf_malloc_first_start_attempt"), args)
  let prefix = startup_lemma(
    "tlsf_full_malloc_start_prefix",
    page_quantify(vars) +
    malloc_start_attempt_cond() +
    " → sl_abort_m(" +
    startup_env() +
    "," +
    p +
    ",tlsf_malloc_full_prefix(" +
    page_arguments(malloc_env_variables()) +
    ")," +
    q +
    "," +
    malloc_start_init_abort() +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("tlsf_sl_abort_m_of_r")),
      @simp.pure_rewrite_tac(ths([thm("tlsf_malloc_full_prefix")])),
      @tactics.match_mp_tac(thm("tlsf_sl_abort_r_block")),
      beta_goal(),
      @tactics.conv_tac(
        norm_conv(extra=[@equal.beta_rule(arity), thm("tbv_results")]),
      ),
      free_apply(
        @simp.pure_rewrite_rule(ths([thm("tlsf_malloc_first_body")]))(first),
      ),
    ]),
  )
  let a = malloc_start_ready_model()
  let vtail = malloc_case_variables().filter(x => {
    !["G", "rp", "labels"].contains(x.0)
  })
  let sourceargs = vtail.map(x => {
    if x.0 == "before" {
      "(prepared : \{heap})"
    } else if x.0 == "fp" {
      malloc_start_frozen()
    } else if page_model_variables().map(x => x.0).search(x.0) is Some(i) {
      a[i]
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let source = inst(thm("tlsf_full_malloc_after_first"), sourceargs)
  let fullq = malloc_start_full_post()
  let ab = malloc_start_abort()
  let cond = malloc_start_attempt_cond() + " && (" + malloc_full_natives() + ")"
  let _ = startup_lemma(
    "tlsf_full_malloc_start_tail",
    page_quantify(vars) +
    cond +
    " → tlsf_sl_abort_r(" +
    startup_env() +
    "," +
    fullq +
    "," +
    q +
    ",tlsf_malloc_start_full_tail(" +
    page_arguments(malloc_env_variables()) +
    ")," +
    fullq +
    ",[" +
    fullq +
    "]," +
    ab +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_malloc_start_model_facts"), [
              "(d : \{w32})",
              "(lim : Num)",
            ]),
            g,
          ),
        )(g)
      },
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_initialize_limit_bounds"), [
              "(d : \{w32})",
              "(lim : Num)",
            ]),
            g,
          ),
        )(g)
      },
      startup_intro_ex(),
      startup_weaken(
        source,
        seq([free_apply(source), startup_vc()]),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.repeat_tac(@tactics.gen_tac),
                beta_goal(),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                free_apply(
                  inst(thm("tlsf_malloc_start_full_outcome"), [
                    "(d : \{w32})",
                    "(lim : Num)",
                    n,
                    "(before : \{heap})",
                    "(fp : \{rty})",
                    "(prepared : \{heap})",
                    "(vs : List[Value])",
                    "(gs : List[Value])",
                    "(ms : Num)",
                    "(h : \{heap})",
                  ]),
                ),
                startup_vc(),
              ]),
            ),
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              beta_goal(),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              @simp.rewrite_tac(ths([thm("tlsf_malloc_start_abort")])),
              @tactics.disj2_tac,
              free_apply(
                inst(thm("tlsf_malloc_start_state_frame"), [
                  "(d : \{w32})",
                  "(lim : Num)",
                  "(fp : \{rty})",
                  a[1],
                  "(gs : List[Value])",
                  "(ms : Num)",
                  "(h : \{heap})",
                ]),
              ),
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ]),
        ),
      ),
    ]),
  )
  let _ = startup_lemma(
    "tlsf_full_malloc_start_nonzero",
    page_quantify(vars) +
    cond +
    " → tlsf_sl_abort_r(" +
    startup_env() +
    "," +
    fullq +
    "," +
    p +
    ",tlsf_full_malloc_code(" +
    page_arguments(malloc_env_variables()) +
    ")," +
    fullq +
    ",[" +
    fullq +
    "]," +
    ab +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.pure_rewrite_tac(ths([thm("tlsf_malloc_start_full_parts")])),
      @tactics.match_mp_tac(thm("tlsf_sl_abort_r_seq")),
      @tactics.exists_tac(tm(q)),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          g => {
            let pr = startup_r_of_m(prefix, fullq, "[" + fullq + "]")
            startup_conseq(
              pr,
              free_apply(pr),
              startup_vc(extra=[thm("tlsf_malloc_start_abort")]),
            )(g)
          },
          free_apply(inst(thm("tlsf_full_malloc_start_tail"), args)),
        ]),
      ),
    ]),
  )
}
