// Transport successful allocations and consistent failure states back to the
// original client-frame interpretation, even when startup and retry both grow.

///|
fn startup_result_transport() -> @tactics.Tactic {
  g => {
    @tactics.first_assum(th => {
      guard args_of(@kernel.concl(th), "tlsf_malloc_result", 8) is Some(a) else {
        return @tactics.no_tac
      }
      let rule = inst(thm("tlsf_malloc_result_original_frame"), [
        show(a[0]),
        show(a[1]),
        "(lim : Num)",
        "(fp : " + rty + ")",
        show(a[4]),
        show(a[5]),
        show(a[6]),
        show(a[7]),
        show(a[2]),
      ])
      g => @tactics.assume_tac(block_under(rule, g))(g)
    })(g)
  }
}

///|
fn prove_tlsf_malloc_start_outcomes() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let n = "(n : " + w32 + ")"
  let next = "tlsf_initialize_limit(" + d + "," + lim + ")"
  let a = malloc_start_model(d, next)
  let frozen = malloc_start_frozen()
  let vars = [
    ("d", w32),
    ("lim", "Num"),
    ("n", w32),
    ("before", heap),
    ("fp", rty),
    ("prepared", heap),
    ("res", "List[Value]"),
    ("gs", "List[Value]"),
    ("ms", "Num"),
    ("h", heap),
  ]
  for full in [false, true] {
    let name = if full { "full" } else { "try" }
    let source = "tlsf_" +
      name +
      "_malloc_post(" +
      (a + [n, "(prepared : " + heap + ")", frozen]).join(",") +
      ")"
    let target = "tlsf_" +
      name +
      "_malloc_start_post(" +
      [d, n, lim, "(before : " + heap + ")", "(fp : " + rty + ")"].join(",") +
      ")"
    let _ = startup_lemma(
      "tlsf_malloc_start_" + name + "_outcome",
      page_quantify(vars) +
      "tlsf_initialize_valid(" +
      d +
      "," +
      lim +
      ") && !(" +
      n +
      " == word(0)) && " +
      source +
      "(res,gs,ms,h) → " +
      target +
      "(res,gs,ms,h)",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_initialize_limit_bounds"), [d, lim]), g),
          )(g)
        },
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) != "tlsf_" + name + "_malloc_post" {
            return @tactics.no_tac
          }
          @tactics.strip_assume_tac(
            @simp.rewrite_rule(ths([thm("tlsf_" + name + "_malloc_post")]))(th),
          )
        }),
        subst_vars(),
        @tactics.try_tac(solve(@simp.asm_rewrite_tac(ths([])))),
        @tactics.try_tac(startup_result_transport()),
        @simp.rewrite_tac(ths([thm("tlsf_" + name + "_malloc_start_post")])),
        @tactics.first(
          @list.List([
            solve(startup_vc()),
            solve(
              seq([
                @tactics.disj2_tac,
                if full {
                  @tactics.all_tac
                } else {
                  @tactics.disj1_tac
                },
                @tactics.first_assum(th => {
                  guard args_of(@kernel.concl(th), "tlsf_malloc_result", 8)
                    is Some(r) else {
                    return @tactics.no_tac
                  }
                  if !@basics.aconv(r[2], tm(lim)) {
                    return @tactics.no_tac
                  }
                  seq([
                    @tactics.exists_tac(r[4]),
                    @simp.asm_rewrite_tac(ths([])),
                  ])
                }),
              ]),
            ),
            solve(
              seq([
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @simp.asm_rewrite_tac(
                  ths([thm("tlsf_malloc_start_initialized"), @class.eta_ax()]),
                ),
              ]),
            ),
          ]),
        ),
      ]),
    )
  }
  let _ = startup_lemma(
    "tlsf_malloc_start_state_frame",
    "∀ d : " +
    w32 +
    ", ∀ lim : Num, ∀ fp : " +
    rty +
    ", ∀ next : Num, ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", lim <= next && tlsf_malloc_state(d,next," +
    frozen +
    ",gs,ms,h) → tlsf_malloc_state(d,lim,fp,gs,ms,h)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("tlsf_malloc_state")])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          seq([
            seq(
              page_model_variables()[2:]
              .to_owned()
              .map(x => @tactics.exists_tac(tm("(" + x.0 + " : " + x.1 + ")"))),
            ),
            @simp.asm_rewrite_tac(ths([])),
            @int.asm_arith_tac,
          ]),
        ]),
      ),
    ]),
  )
}
