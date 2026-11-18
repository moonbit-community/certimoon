// Continue the full allocator after its first attempt, retaining both the
// consistent arena on OOM and the original client frame after a retry.

///|
fn startup_attempt_ent(
  a : Array[String],
  n : String,
  fast : Bool,
) -> @tactics.Tactic raise {
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    beta_goal(),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    g => {
      @tactics.strip_assume_tac(
        block_under(
          inst(
            thm(
              if fast {
                "tlsf_malloc_try_available"
              } else {
                "tlsf_malloc_try_no_fit"
              },
            ),
            a +
            [
              n,
              "(before : \{heap})",
              "(fp : \{rty})",
              "(vs : List[Value])",
              "(gs : List[Value])",
              "(ms : Num)",
              "(h : \{heap})",
            ],
          ),
          g,
        ),
      )(g)
    },
    subst_vars(),
    seq(
      ["out0", "out1", "out2", "out3", "out4"].map(x => {
        @tactics.exists_tac(tm("(" + x + " : Value)"))
      }),
    ),
    @simp.asm_rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
    @tactics.try_tac(startup_meson(ths([]))),
  ])
}

///|
fn prove_tlsf_malloc_start_tail() -> Unit raise {
  let a = block_model_args()
  let n = "(n : \{w32})"
  let vars = malloc_case_variables().filter(x => {
    !["G", "rp", "labels"].contains(x.0)
  })
  let q = body_post(
    "tlsf_full_malloc_post(" +
    (a + [n, "(before : \{heap})", "(fp : \{rty})"]).join(",") +
    ")",
  )
  let ab = malloc_abort_post(a)
  let sourceargs = malloc_case_variables().map(x => {
    if x.0 == "G" {
      startup_false_specs()
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let fast = inst(thm("tlsf_full_malloc_fast_tail"), sourceargs)
  let slow = inst(
    thm("tlsf_full_malloc_slow_tail"),
    vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
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
  let _ = startup_lemma(
    "tlsf_full_malloc_after_first",
    page_quantify(vars) +
    cond +
    " → tlsf_sl_abort_r(" +
    startup_env() +
    "," +
    q +
    "," +
    malloc_attempt_post("first", a, n) +
    ",tlsf_malloc_start_full_tail(" +
    page_arguments(malloc_env_variables()) +
    ")," +
    q +
    ",[" +
    q +
    "]," +
    ab +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @class.asm_cases_tac(tm(malloc_available(a, n))),
      g => {
        let f = startup_r_of_g(fast, ab)
        let s = startup_r_of_m(slow, q, "[" + q + "]")
        @tactics.first(
          @list.List([
            solve(
              startup_conseq(f, free_apply(f), startup_attempt_ent(a, n, true)),
            ),
            solve(
              startup_conseq(s, free_apply(s), startup_attempt_ent(a, n, false)),
            ),
          ]),
        )(g)
      },
    ]),
  )
}
