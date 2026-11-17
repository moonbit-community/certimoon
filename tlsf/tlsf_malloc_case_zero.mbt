// The zero request returns before accessing allocator memory.

///|
fn prove_tlsf_malloc_case_zero() -> Unit raise {
  let a = block_model_args()
  let n = "(word(0) : " + w32 + ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  for v in malloc_variant_names() {
    let initlc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let q = malloc_attempt_post(v, a, n)
    let g = malloc_g_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    let env = malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    let dead = ["small", "large"].map(part => {
      inst(thm("tlsf_malloc_" + v + "_dead_" + part), g + env)
    })
    let code = malloc_part(v, "body")
    let afters = malloc_continuations(malloc_program_code(code)).map(_ => {
      malloc_false()
    })
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_zero_case",
        page_quantify(malloc_case_variables()) +
        "sl_triple_g((G : " +
        malloc_g_variables()[0].1 +
        "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
        (if v == "try" { q } else { "(rp : " + sassn + ")" }) +
        ",st(NIL," +
        initlc +
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
        Array::make(1, malloc_vc()),
        afters~,
        chunks=dead,
        rws=malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
