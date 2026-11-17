///|
fn malloc_slow_prefix_post(a : Array[String], n : String) -> String {
  let work = ["out0", "out1", "out2", "out3", "out4"]
  let lc = "[" +
    ([malloc_i(n)] + work.map(x => "(" + x + " : Value)")).join(",") +
    "]"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => " +
  work.map(x => "∃ " + x + " : Value, ").join("") +
  "st([" +
  malloc_i("word(4294967295)") +
  "]," +
  lc +
  "," +
  r +
  ")(vs,lc,gs,ms,h)"
}

///|
fn prove_tlsf_malloc_slow_prefix() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let vars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let source = inst(
    thm("tlsf_malloc_first_block"),
    vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
  )
  let t = args_of(@basics.dest_imp(@kernel.concl(source)).1, "sl_triple_m", 7).unwrap()
  let need = show(@basics.dest_imp(@kernel.concl(source)).0)
  let _ = lemma(
    "tlsf_malloc_slow_prefix",
    page_quantify(vars) +
    "(" +
    need +
    ") && !" +
    malloc_available(a, n) +
    " → sl_triple_m(" +
    page_arguments(malloc_g_variables()[1:4].to_owned()) +
    "," +
    show(t[3]) +
    "," +
    show(t[4]) +
    "," +
    malloc_slow_prefix_post(a, n) +
    ",NIL)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(t[3]),
      @tactics.exists_tac(t[5]),
      @simp.rewrite_tac(ths([@class.eta_ax(), @lists.append()])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(same_tac()),
          solve(free_apply(source)),
          solve(
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              beta_goal(),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              g => {
                @tactics.mp_tac(
                  block_under(
                    inst(
                      thm("tlsf_malloc_try_no_fit"),
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
                    g,
                  ),
                )(g)
              },
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              subst_vars(),
              seq(
                ["out0", "out1", "out2", "out3", "out4"].map(x => {
                  @tactics.exists_tac(tm("(" + x + " : Value)"))
                }),
              ),
              @simp.asm_rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
            ]),
          ),
        ]),
      ),
    ]),
  )
}

///|
fn prove_tlsf_malloc_early_failure() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let lc = malloc_request_locals(
    "first", n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
  )
  let after = malloc_request_locals(
    "first",
    n,
    malloc_i("word(4294967295)"),
    "(l1 : Value)",
    "(l2 : Value)",
    "(l3 : Value)",
    "(l4 : Value)",
  )
  let vars = malloc_case_variables() + [("R", rty)]
  ignore(
    sym_prove(
      "tlsf_malloc_early_failure",
      page_quantify(vars) +
      "sl_triple(st([" +
      malloc_i("word(4294967295)") +
      "]," +
      lc +
      ",(R : " +
      rty +
      ")),tlsf_malloc_full_early(" +
      page_arguments(malloc_env_variables()) +
      "),st(NIL," +
      after +
      ",R))",
      [],
      [malloc_vc()],
      kind="lemma",
    ),
  )
  let _ = a
}
