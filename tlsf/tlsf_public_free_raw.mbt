///|
fn prove_tlsf_public_free_raw() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let vars = malloc_g_variables() +
    [("pop", "Num"), ("push", "Num"), ("free_idx", "Num")] +
    page_model_variables() +
    [("p", w), ("b", w), ("l2", "Value"), ("fp", rty)]
  for small in [false, true] {
    let cap = if small {
      a[9] + "(" + p + ")"
    } else {
      "val(tlsf_size(" + a[4] + "(" + b + ")))"
    }
    let tag = if small { "(word(4) : " + w + ")" } else { a[4] + "(" + b + ")" }
    let r = public_free_r(a, b, cap, fp)
    let cond = if small {
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
      "MEM(" + b + "," + a[3] + ")"
    }
    let lc = "[" +
      malloc_i("word_add(" + b + ",word(8))") +
      "," +
      malloc_i(a[0]) +
      ",(l2 : Value)]"
    let lc2 = "[" +
      malloc_i("word_add(" + b + ",word(8))") +
      "," +
      malloc_i(b) +
      ",(l2 : Value)]"
    ignore(
      sym_prove(
        "tlsf_public_free_" + (if small { "small" } else { "large" }) + "_read",
        page_quantify(vars) +
        cond +
        " → sl_triple_g(" +
        malloc_g_env() +
        ",st(NIL," +
        lc +
        "," +
        r +
        "),tlsf_public_free_read(d,free_idx),st([" +
        malloc_i("word_and(" + tag + ",word(4))") +
        "]," +
        lc2 +
        "," +
        r +
        "),(labels : List[" +
        sassn +
        "]))",
        [],
        () => Array::make(1, public_free_vc()),
        rules=step_rules +
          [
            "st_public_free_" +
            (if small { "small" } else { "large" }) +
            "_header",
          ],
        rws=[thm("tlsf_public_free_unpayload")],
        kind="lemma",
      ),
    )
  }
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = b
  let lc = "[" +
    malloc_i("word_add(" + m + ",word(8))") +
    "," +
    malloc_i(m) +
    ",(l2 : Value)]"
  let cap = "val(tlsf_size(" + a[4] + "(" + m + ")))"
  let r = public_free_r(a, m, cap, fp)
  let cond = block_backing(a) +
    " && MEM(" +
    m +
    "," +
    a[3] +
    ") && !MEM(" +
    m +
    "," +
    a[8] +
    ") && tlsf_used(" +
    a[4] +
    "(" +
    m +
    ")) && " +
    block_native_hyp()
  ignore(
    sym_prove(
      "tlsf_public_free_large_branch",
      page_quantify(vars) +
      cond +
      " → sl_triple_g(" +
      malloc_g_env() +
      ",st(NIL," +
      lc +
      "," +
      r +
      "),tlsf_public_free_large(d,free_idx)," +
      public_free_result(a, fp) +
      ",(labels : List[" +
      sassn +
      "]))",
      [],
      () => [public_free_vc(extra=[thm("st")])],
      chunks=[thm("tlsf_public_free_large_call_g")],
      kind="lemma",
    ),
  )
  for small in [false, true] {
    let cap = if small {
      a[9] + "(" + p + ")"
    } else {
      "val(tlsf_size(" + a[4] + "(" + b + ")))"
    }
    let tag = if small { "(word(4) : " + w + ")" } else { a[4] + "(" + b + ")" }
    let r = public_free_r(a, b, cap, fp)
    let cond = (if small {
        "MEM(" + p + "," + a[8] + ") && MEM(" + b + "," + a[12] + "(" + p + "))"
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
        ")) && word_and(" +
        tag +
        ",word(4)) == word(0)"
      }) +
      " && " +
      block_native_hyp()
    let _ = lemma(
      "tlsf_public_free_" + (if small { "small" } else { "large" }) + "_choose",
      page_quantify(vars) +
      cond +
      " → sl_triple_g(" +
      malloc_g_env() +
      ",st([" +
      malloc_i("word_and(" + tag + ",word(4))") +
      "]," +
      lc +
      "," +
      r +
      "),tlsf_public_free_choose(d,free_idx)," +
      public_free_result(a, fp) +
      ",(labels : List[" +
      sassn +
      "]))",
      () => {
        seq([
          gen,
          strip,
          @simp.pure_rewrite_tac(ths([thm("tlsf_public_free_choose")])),
          @logic.match_mp_tac(
            thm(
              "tlsf_block_free_if_" + (if small { "taken" } else { "skipped" }),
            ),
          ),
          @tactics.conj_tac,
          @tactics.first(
            @list.List([
              solve(
                seq([
                  @simp.asm_rewrite_tac(ths([])),
                  @tactics.conv_tac(@words.word_reduce_conv),
                ]),
              ),
              seq([
                @tactics.gen_tac,
                free_apply(
                  @simp.pure_rewrite_rule(
                    ths([
                      thm(
                        if small {
                          "tlsf_block_free_code"
                        } else {
                          "tlsf_public_free_large"
                        },
                      ),
                    ]),
                  )(
                    thm(
                      "tlsf_public_free_" +
                      (if small { "small" } else { "large" }) +
                      "_branch",
                    ),
                  ),
                ),
              ]),
            ]),
          ),
        ])
      },
    )
  }
}
