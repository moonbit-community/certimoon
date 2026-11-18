///|
fn prove_tlsf_malloc_start_model() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let next = "tlsf_initialize_limit(" + d + "," + lim + ")"
  let a = malloc_start_model(d, next)
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let _ = startup_lemma(
    "tlsf_malloc_start_model_facts",
    "∀ d : " +
    w32 +
    ", ∀ lim : Num, tlsf_initialize_valid(d,lim) → " +
    physical +
    " && " +
    block_backing(a) +
    " && " +
    block_lists(a) +
    " && (" +
    malloc_guard_cond(a) +
    ")",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_initialize_limit_bounds"), [d, lim])),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([thm("tlsf_initialize_valid")])),
      ),
      split_conjs(),
      have(
        physical,
        seq([
          free_apply(inst(thm("tlsf_initialize_physical"), [d, next])),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
      g => {
        @tactics.strip_assume_tac(
          block_under(inst(thm("tlsf_malloc_guard_facts"), a), g),
        )(g)
      },
      @simp.asm_rewrite_tac(
        ths([
          thm("tlsf_small_backing"),
          thm("tlsf_small_lists_ok"),
          @lists.mem(),
        ]),
      ),
    ]),
  )
}

///|
fn prove_tlsf_malloc_start_resume() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let n = "(n : " + w32 + ")"
  let next = "tlsf_initialize_limit(" + d + "," + lim + ")"
  let a = malloc_start_model(d, next)
  let vars = malloc_g_variables() +
    malloc_env_variables() +
    [
      ("pop", "Num"),
      ("push", "Num"),
      ("lim", "Num"),
      ("n", w32),
      ("before", heap),
      ("fp", rty),
      ("prepared", heap),
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  let args = malloc_case_variables().map(x => {
    if x.0 == "fp" {
      malloc_start_frozen()
    } else if x.0 == "before" {
      "(prepared : " + heap + ")"
    } else if page_model_variables().map(x => x.0).search(x.0) is Some(i) {
      a[i]
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  for v in ["try", "first"] {
    for part in ["fresh", "large"] {
      let source = inst(
        thm("tlsf_malloc_" + v + "_resume_" + part + "_case"),
        args,
      )
      let conclusion = show(@basics.dest_imp(@kernel.concl(source)).1)
      let bounds = if part == "fresh" {
        "0 < val(" + n + ") && val(" + n + ") <= 256"
      } else {
        "256 < val(" + n + ") && val(" + n + ") <= 4160749568"
      }
      let _ = startup_lemma(
        "tlsf_malloc_start_" + v + "_" + part,
        page_quantify(vars) +
        "tlsf_initialize_valid(" +
        d +
        "," +
        lim +
        ") && " +
        bounds +
        " && (" +
        malloc_helper_natives() +
        ") → " +
        conclusion,
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            @tactics.strip_assume_tac(
              block_under(
                inst(thm("tlsf_malloc_start_model_facts"), [d, lim]),
                g,
              ),
            )(g)
          },
          if part == "fresh" {
            g => {
              @tactics.strip_assume_tac(
                block_under(inst(thm("tlsf_malloc_request_setup"), [n]), g),
              )(g)
            }
          } else {
            @tactics.all_tac
          },
          free_apply(source),
          malloc_vc(extra=[@lists.mem()]),
        ]),
      )
    }
  }
}
