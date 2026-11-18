// A zero request exits without reading or initializing allocator metadata.

///|
fn prove_tlsf_malloc_start_zero() -> Unit raise {
  let zero = malloc_i("word(0)")
  for full in [false, true] {
    let v = if full { "first" } else { "try" }
    let name = if full { "full" } else { "try" }
    let q = body_post(
      "tlsf_" +
      name +
      "_malloc_start_post((d : \{w32}),word(0),(lim : Num),(before : \{heap}),(fp : \{rty}))",
    )
    let lc = malloc_request_locals(
      v,
      "(word(0) : \{w32})",
      "(l0 : Value)",
      "(l1 : Value)",
      "(l2 : Value)",
      "(l3 : Value)",
      "(l4 : Value)",
    )
    let code = if full {
      "tlsf_full_malloc_code(" + page_arguments(malloc_env_variables()) + ")"
    } else {
      malloc_part("try", "body")
    }
    let first = @basics.dest_list(malloc_program_code(code)).head().unwrap()
    let afters = malloc_continuations(malloc_program_code(code)).map(x => {
      if full && x == first {
        "st([" + zero + "]," + lc + "," + malloc_start_saved() + ")"
      } else {
        malloc_false()
      }
    })
    let vars = [("G", malloc_g_variables()[0].1)] +
      malloc_start_vars().filter(x => x.0 != "n") +
      [
        ("l0", "Value"),
        ("l1", "Value"),
        ("l2", "Value"),
        ("l3", "Value"),
        ("l4", "Value"),
      ]
    let deadargs = malloc_g_variables().map(x => "(" + x.0 + " : " + x.1 + ")") +
      malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    ignore(
      sym_prove(
        "tlsf_" + name + "_malloc_start_zero",
        page_quantify(vars) +
        "sl_triple_g((G : " +
        malloc_g_variables()[0].1 +
        ")," +
        startup_env() +
        "," +
        q +
        ",st(NIL," +
        lc +
        "," +
        malloc_start_saved() +
        ")," +
        code +
        "," +
        q +
        ",[" +
        q +
        "])",
        [],
        () => {
          Array::make(
            if full {
              3
            } else {
              1
            },
            @tactics.first(
              @list.List([
                solve(
                  startup_vc(extra=[thm("tlsf_" + name + "_malloc_start_post")]),
                ),
                malloc_vc(extra=[thm("tlsf_" + name + "_malloc_start_post")]),
              ]),
            ),
          )
        },
        afters~,
        chunks=["small", "large"].map(part => {
          inst(thm("tlsf_malloc_" + v + "_dead_" + part), deadargs)
        }),
        rws=[thm("tlsf_" + name + "_malloc_start_post")] +
          malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
