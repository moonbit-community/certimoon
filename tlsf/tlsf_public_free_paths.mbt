// Compose the exact guard, dispatch read, chosen branch and dropped result.

///|
fn prove_tlsf_public_free_paths() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let b = "(b : " + w + ")"
  let p = "(p : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let ptr = "word_add(" + b + ",word(8))"
  let vars = malloc_g_variables() +
    [("pop", "Num"), ("push", "Num"), ("free_idx", "Num")] +
    page_model_variables() +
    [("p", w), ("b", w), ("l1", "Value"), ("l2", "Value"), ("fp", rty)]
  let guard_cond = "!word_ugt(" +
    a[0] +
    ",word(4294965088)) && !word_ult(" +
    ptr +
    ",word_add(tlsf_base(" +
    a[0] +
    "),word(2184)))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let gvars = malloc_g_variables().map(v => "(" + v.0 + " : " + v.1 + ")")
  let native = block_native_hyp()
  let code = "tlsf_public_free_body(d,free_idx)"
  let smallcode = malloc_program_code("tlsf_block_free_code(d,free_idx)")
  for small in [false, true] {
    let cap = if small {
      a[9] + "(" + p + ")"
    } else {
      "val(tlsf_size(" + a[4] + "(" + b + ")))"
    }
    let r = public_free_r(a, b, cap, fp)
    let lc = "[" + malloc_i(ptr) + ",(l1 : Value),(l2 : Value)]"
    let lc1 = "[" + malloc_i(ptr) + "," + malloc_i(a[0]) + ",(l2 : Value)]"
    let facts = if small {
      block_backing(a) +
      " && " +
      block_lists(a) +
      " && MEM(" +
      p +
      "," +
      a[8] +
      ") && MEM(" +
      b +
      "," +
      a[12] +
      "(" +
      p +
      "))"
    } else {
      block_backing(a) +
      " && MEM(" +
      b +
      "," +
      a[3] +
      ") && !MEM(" +
      b +
      "," +
      a[8] +
      ") && tlsf_used(" +
      a[4] +
      "(" +
      b +
      "))"
    }
    let tag = if small {
      "T"
    } else {
      "word_and(" + a[4] + "(" + b + "),word(4)) == word(0)"
    }
    let afters = malloc_continuations(malloc_program_code(code)).map(instr => {
      if args_of(instr, "If", 3) is Some([_, yes, _]) {
        if @basics.aconv(yes, smallcode) {
          public_free_result(a, fp)
        } else if @basics.dest_list(yes).length() == 1 &&
          head_name(@basics.dest_list(yes).head().unwrap()) == "Unreachable" {
          "st(NIL," + lc1 + "," + r + ")"
        } else {
          malloc_false()
        }
      } else {
        malloc_false()
      }
    })
    let path = sym_prove(
      "tlsf_public_free_" + (if small { "small" } else { "large" }) + "_path",
      page_quantify(vars) +
      facts +
      " && " +
      guard_cond +
      " && " +
      tag +
      " && " +
      native +
      " → sl_triple_g(" +
      malloc_g_env() +
      ",st(NIL," +
      lc +
      "," +
      r +
      ")," +
      code +
      "," +
      public_free_post(a, fp) +
      ",(labels : List[" +
      sassn +
      "]))",
      [],
      () => Array::make(3, public_free_final_vc()),
      afters~,
      chunks=[
        thm("tlsf_public_free_guard_live"),
        thm(
          "tlsf_public_free_" +
          (if small { "small" } else { "large" }) +
          "_read",
        ),
        thm(
          "tlsf_public_free_" +
          (if small { "small" } else { "large" }) +
          "_choose",
        ),
      ],
      rws=[thm("tlsf_public_free_unpayload")],
      kind="lemma",
    )
    let _ = lemma(
      "tlsf_public_free_" + (if small { "small" } else { "large" }) + "_case",
      page_quantify(vars) +
      "tlsf_physical_ok(" +
      a[:5].to_owned().join(",") +
      ") && " +
      facts +
      " && " +
      native +
      " → sl_triple_g(" +
      malloc_g_env() +
      ",st(NIL," +
      lc +
      "," +
      r +
      ")," +
      code +
      "," +
      public_free_post(a, fp) +
      ",(labels : List[" +
      sassn +
      "]))",
      () => {
        seq([
          gen,
          strip,
          g => {
            @tactics.strip_assume_tac(
              block_under(inst(thm("tlsf_malloc_guard_facts"), a), g),
            )(g)
          },
          if small {
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_public_free_small_geometry"), a + [p, b]),
                  g,
                ),
              )(g)
            }
          } else {
            seq([
              g => {
                @tactics.strip_assume_tac(
                  block_under(
                    inst(thm("tlsf_public_free_block_geometry"), a + [b]),
                    g,
                  ),
                )(g)
              },
              free_have(
                "val(" + b + ")+8 < 4294967296",
                seq([
                  @tactics.undisch_tac(
                    tm(
                      "tlsf_block_ok(val(" +
                      b +
                      ")," +
                      a[1] +
                      "," +
                      b +
                      "," +
                      a[4] +
                      ")",
                    ),
                  ),
                  @simp.rewrite_tac(ths([thm("tlsf_block_ok")])),
                  strip,
                  @int.asm_arith_tac,
                ]),
              ),
              g => {
                @tactics.strip_assume_tac(
                  block_under(
                    inst(thm("tlsf_public_free_pointer_guard"), [a[0], b]),
                    g,
                  ),
                )(g)
              },
            ])
          },
          free_apply(
            inst(
              path,
              gvars +
              ["(pop : Num)", "(push : Num)", "(free_idx : Num)"] +
              a +
              [p, b, "(l1 : Value)", "(l2 : Value)", fp],
            ),
          ),
          public_free_vc(),
        ])
      },
    )
  }
}
