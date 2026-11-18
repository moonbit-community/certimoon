// Nonzero requests cross the entry's early-zero exit without changing memory.

///|
fn prove_tlsf_malloc_start_heads() -> Unit raise {
  let n = "(n : \{w32})"
  let vars = malloc_g_variables().filter(x => x.0 != "labels") +
    malloc_env_variables() +
    [
      ("L", sassn),
      ("n", w32),
      ("R", rty),
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  for v in ["try", "first"] {
    let lc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_start_head_all",
        page_quantify(vars) +
        "!(" +
        n +
        " == word(0)) → sl_triple_g(" +
        malloc_g_env() +
        ",st(NIL," +
        lc +
        ",(R : \{rty}))," +
        malloc_part(v, "start_head") +
        ",st(NIL," +
        lc +
        ",R),[(L : \{sassn})])",
        [],
        () => Array::make(1, malloc_vc()),
        kind="lemma",
      ),
    )
  }
}

///|
fn prove_tlsf_malloc_start_tails() -> Unit raise {
  let a = block_model_args()
  let n = "(n : \{w32})"
  let post = body_post(
    "tlsf_full_malloc_post(" +
    (a + [n, "(before : \{heap})", "(fp : \{rty})"]).join(",") +
    ")",
  )
  let code = "tlsf_malloc_start_full_tail(" +
    page_arguments(malloc_env_variables()) +
    ")"
  ignore(
    sym_prove(
      "tlsf_full_malloc_fast_tail",
      page_quantify(malloc_case_variables()) +
      "val(" +
      n +
      ") <= 4160749568 && (" +
      malloc_helper_natives() +
      ") && " +
      malloc_available(a, n) +
      " → sl_triple_g((G : " +
      malloc_g_variables()[0].1 +
      ")," +
      startup_env() +
      "," +
      post +
      "," +
      malloc_fast_prefix_post(a, n) +
      "," +
      code +
      "," +
      post +
      ",[" +
      post +
      "])",
      [],
      () => Array::make(10, malloc_vc(extra=[thm("tlsf_full_malloc_post")])),
      afters=malloc_continuations(malloc_program_code(code)).map(_ => {
        malloc_false()
      }),
      rws=[thm("tlsf_full_malloc_post")] + malloc_extra_rewrites(),
      kind="lemma",
    ),
  )
}
