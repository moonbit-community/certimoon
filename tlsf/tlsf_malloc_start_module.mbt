// Closed contracts for calls to the actual lazy-initializing native closures.

///|
fn prove_tlsf_malloc_start_modules() -> Unit raise {
  let n = "(n : \{w32})"
  let zero = malloc_i("word(0)")
  let basevars = malloc_start_vars()
  for full in [false, true] {
    let name = if full { "full" } else { "try" }
    let count = if full { 5 } else { 4 }
    let post = "tlsf_" +
      name +
      "_malloc_start_post((d : \{w32})," +
      n +
      ",(lim : Num),(before : \{heap}),(fp : \{rty}))"
    let q = body_post(post)
    let ab = if full { malloc_start_abort() } else { malloc_start_init_abort() }
    let r = malloc_start_saved()
    let lc = "[" + ([malloc_i(n)] + Array::make(count, zero)).join(",") + "]"
    let code = if full {
      "tlsf_full_malloc_code(" + page_arguments(malloc_env_variables()) + ")"
    } else {
      "tlsf_try_malloc_code((d : \{w32}),(initialize_idx : Num),(page_idx : Num),(take_idx : Num))"
    }
    let cond = "tlsf_initialize_valid((d : \{w32}),(lim : Num)) && val(" +
      n +
      ") <= 4160749568 && " +
      malloc_start_initialize_native() +
      " && " +
      malloc_start_push_native() +
      " && (" +
      (if full { malloc_full_natives() } else { malloc_helper_natives() }) +
      ")"
    let body = startup_lemma(
      "tlsf_" + name + "_malloc_start_body",
      page_quantify(basevars) +
      cond +
      " → tlsf_sl_abort_r(" +
      startup_env() +
      "," +
      q +
      ",st(NIL," +
      lc +
      "," +
      r +
      ")," +
      code +
      "," +
      q +
      ",[" +
      q +
      "]," +
      ab +
      ")",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @class.asm_cases_tac(tm(n + " == word(0)")),
        @tactics.first(
          @list.List([
            solve(
              seq([
                subst_only("n"),
                g => {
                  let zvars = [("G", malloc_g_variables()[0].1)] +
                    malloc_start_vars().filter(x => x.0 != "n") +
                    [
                      ("l0", "Value"),
                      ("l1", "Value"),
                      ("l2", "Value"),
                      ("l3", "Value"),
                      ("l4", "Value"),
                    ]
                  let source = inst(
                    thm("tlsf_" + name + "_malloc_start_zero"),
                    zvars.map(x => {
                      if x.0 == "G" {
                        startup_false_specs()
                      } else if ["l0", "l1", "l2", "l3", "l4"].contains(x.0) {
                        zero
                      } else {
                        "(" + x.0 + " : " + x.1 + ")"
                      }
                    }),
                  )
                  let rw = ths(
                    if full {
                      []
                    } else {
                      [thm("tlsf_try_malloc_code"), thm("tlsf_malloc_try_body")]
                    },
                  )
                  seq([
                    @simp.pure_rewrite_tac(rw),
                    startup_lift_g(@simp.pure_rewrite_rule(rw)(source)),
                  ])(g)
                },
              ]),
            ),
            seq([
              free_have(
                "0 < val(" + n + ")",
                seq([
                  @tactics.undisch_tac(tm("!(" + n + " == word(0))")),
                  @simp.rewrite_tac(ths([@equal.gsym(@words.val_eq_0())])),
                  @int.arith_tac,
                ]),
              ),
              g => {
                let args = (basevars +
                [
                  ("l0", "Value"),
                  ("l1", "Value"),
                  ("l2", "Value"),
                  ("l3", "Value"),
                  ("l4", "Value"),
                ]).map(x => {
                  if ["l0", "l1", "l2", "l3", "l4"].contains(x.0) {
                    zero
                  } else {
                    "(" + x.0 + " : " + x.1 + ")"
                  }
                })
                let source = inst(
                  thm(
                    if full {
                      "tlsf_full_malloc_start_nonzero"
                    } else {
                      "tlsf_malloc_try_start_attempt"
                    },
                  ),
                  args,
                )
                let rw = ths(
                  if full {
                    []
                  } else {
                    [thm("tlsf_try_malloc_code"), thm("tlsf_malloc_try_body")]
                  },
                )
                seq([
                  @simp.pure_rewrite_tac(rw),
                  free_apply(@simp.pure_rewrite_rule(rw)(source)),
                ])(g)
              },
            ]),
          ]),
        ),
      ]),
    )
    let idx = "(" + name + "_idx : Num)"
    let ts = "[" + Array::make(count, "T_num(T_i32)").join(",") + "]"
    let zs = "[" + Array::make(count, zero).join(",") + "]"
    let native = "EL(sfunc_ind((inst : Inst)," +
      idx +
      "),(fs : List[Cl])) == Func_native((inst : Inst),Tf([T_num(T_i32)],[T_num(T_i32)])," +
      ts +
      "," +
      code +
      ")"
    let ar = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => " +
      ab +
      "(NIL,NIL,gs,ms,h)"
    let cq = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => lc == (caller : List[Value]) && " +
      post +
      "(vs,gs,ms,h)"
    let allvars = basevars + [(name + "_idx", "Num"), ("caller", "List[Value]")]
    let rule = inst(thm("tlsf_sl_abort_call_value_r"), [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      malloc_i(n),
      idx,
      ts,
      code,
      zs,
      "(caller : List[Value])",
      r,
      post,
      ar,
    ])
    let normalize = [
      thm("tlsf_initialize_abort"),
      thm("tlsf_malloc_start_abort"),
      @class.eta_ax(),
    ]
    let all = startup_lemma(
      "tlsf_" + name + "_malloc_start_all",
      page_quantify(allvars) +
      cond +
      " && " +
      native +
      " → sl_abort_m(" +
      startup_env() +
      ",st([" +
      malloc_i(n) +
      "],(caller : List[Value])," +
      r +
      "),[Call(" +
      idx +
      ")]," +
      cq +
      "," +
      ab +
      ")",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @simp.pure_rewrite_tac(ths(normalize)),
        beta_goal(),
        @tactics.match_mp_tac(
          @equal.beta_rule(@simp.pure_rewrite_rule(ths(normalize))(rule)),
        ),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(@simp.asm_rewrite_tac(ths([]))),
            solve(
              @simp.rewrite_tac(
                ths([
                  @wasm.thm("n_zeros"),
                  @wasm.thm("bitzero"),
                  @wasm.thm("bitzero_num"),
                  @wasm.thm("map_option"),
                  @lists.map(),
                  @wasm.thm("those"),
                ]),
              ),
            ),
            solve(
              seq([
                @tactics.repeat_tac(@tactics.strip_tac),
                free_apply(thm("tlsf_" + name + "_malloc_start_arity")),
              ]),
            ),
            solve(
              free_apply(
                @equal.beta_rule(
                  @simp.pure_rewrite_rule(ths(normalize))(
                    inst(body, basevars.map(x => "(" + x.0 + " : " + x.1 + ")")),
                  ),
                ),
              ),
            ),
          ]),
        ),
      ]),
    )
    let source = inst(all, allvars.map(x => "(" + x.0 + " : " + x.1 + ")"))
    let (needs, triple) = @basics.dest_imp(@kernel.concl(source))
    let a = args_of(triple, "sl_abort_m", 7).unwrap()
    let runvars = [
      ("fr", hprop),
      ("s", "Wstore"),
      ("f", "Wframe"),
      ("vs", "List[Value]"),
      ("s2", "Wstore"),
      ("f2", "Wframe"),
      ("es2", "List[Einstr]"),
    ]
    let adequate = @bool.ispecl(
      @list.List(a + runvars.map(x => tm("(" + x.0 + " : " + x.1 + ")"))),
      thm("sl_abort_m_adequate"),
    )
    let (need, result) = @basics.dest_imp(@kernel.concl(adequate))
    let prem = ([needs] + @basics.conjuncts(need).to_array()[1:].to_owned())
      .map(x => "(" + show(x) + ")")
      .join(" && ")
    let _ = startup_lemma(
      "tlsf_" + name + "_malloc_start_run",
      page_quantify(allvars + runvars) + prem + " → " + show(result),
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(adequate),
        @simp.asm_rewrite_tac(ths([])),
        free_apply(source),
      ]),
    )
  }
}
