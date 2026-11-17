// Close an allocation entry body against its actual native closure.

///|
fn prove_tlsf_try_malloc_module() -> Unit raise {
  malloc_close_entry("try", 4)
}

///|
fn malloc_close_entry(which : String, locals : Int32) -> Unit raise {
  let w = w32
  let model = page_model_variables() + [("n", w), ("before", heap), ("fp", rty)]
  let a = block_model_args()
  let params = page_arguments(model)
  let ft = "(List[Value],List[Value],Num," + heap + ") -> Bool"
  let prefix = "tlsf_" +
    (if which == "try" { "try_malloc" } else { "full_malloc_fast" })
  let p = if which == "try" {
    "tlsf_try_malloc_pre(" + params + ")"
  } else {
    "tlsf_full_malloc_fast_pre(" + params + ")"
  }
  let q = if which == "try" {
    "tlsf_try_malloc_post(" + params + ")"
  } else {
    "tlsf_full_malloc_post(" + params + ")"
  }
  let idx = if which == "try" { "(try_idx : Num)" } else { "(full_idx : Num)" }
  let envvars = malloc_entry_variables() +
    [("d", w), (if which == "try" { "try_idx" } else { "full_idx" }, "Num")]
  let specparams = "(inst : Inst)," +
    a[0] +
    ",(initialize_idx : Num),(page_idx : Num),(take_idx : Num),(ensure_idx : Num)," +
    idx
  let spec = prefix + "_spec(" + specparams + ")"
  let exvars = model.filter(x => x.0 != "d")
  let exists = exvars.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("")
  if !@logic.names().contains(prefix + "_spec") {
    def(
      prefix + "_spec",
      spec +
      "((j : Num),(P : " +
      ft +
      "),(Q : " +
      ft +
      ")) == (j == sfunc_ind((inst : Inst)," +
      idx +
      ") && (" +
      exists +
      "P == " +
      p +
      " && Q == " +
      q +
      "))",
    )
  }
  let call = lemma(
    prefix + "_spec_call",
    page_quantify(envvars + exvars) +
    spec +
    "(sfunc_ind((inst : Inst)," +
    idx +
    ")," +
    p +
    "," +
    q +
    ")",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(ths([thm(prefix + "_spec")])),
        seq(
          exvars.map(x => @tactics.exists_tac(tm("(" + x.0 + " : " + x.1 + ")"))),
        ),
        @simp.rewrite_tac(ths([])),
      ])
    },
  )
  let ts = "[" + Array::make(locals, "T_num(T_i32)").join(",") + "]"
  let zs = "[" + Array::make(locals, malloc_i("word(0)")).join(",") + "]"
  let code = "tlsf_" +
    (if which == "try" { "try_malloc" } else { "full_malloc" }) +
    "_code(" +
    a[0] +
    ",(initialize_idx : Num),(page_idx : Num),(take_idx : Num)" +
    (if which == "try" { "" } else { ",(ensure_idx : Num)" }) +
    ")"
  let native = "EL(sfunc_ind((inst : Inst)," +
    idx +
    "),(fs : List[Cl])) == Func_native((inst : Inst),Tf([T_num(T_i32)],[T_num(T_i32)])," +
    ts +
    "," +
    code +
    ")"
  let needs = native + " && (" + malloc_helper_natives() + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let specs = lemma(
    prefix + "_specs",
    page_quantify(envvars) +
    needs +
    " → (∀ k : Num, specs_ok(k," +
    spec +
    ",(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)))",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_funs_g")),
        gen,
        @simp.rewrite_tac(ths([thm(prefix + "_spec")])),
        strip,
        subst_vars(),
        seq(
          ["[T_num(T_i32)]", "[T_num(T_i32)]", ts, code, zs].map(x => {
            @tactics.exists_tac(tm(x))
          }),
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
                gen,
                free_apply(
                  inst(
                    thm(prefix + "_body"),
                    [spec] +
                    malloc_entry_variables().map(x => {
                      "(" + x.0 + " : " + x.1 + ")"
                    }) +
                    model.map(x => "(" + x.0 + " : " + x.1 + ")") +
                    ["(args : List[Value])"],
                  ),
                ),
              ]),
            ),
            solve(
              seq([
                gen,
                @simp.rewrite_tac(
                  ths([
                    thm(
                      if which == "try" {
                        "tlsf_try_malloc_pre"
                      } else {
                        "tlsf_full_malloc_fast_pre"
                      },
                    ),
                    thm("tlsf_try_malloc_pre"),
                    thm(
                      if which == "try" {
                        "tlsf_try_malloc_post"
                      } else {
                        "tlsf_full_malloc_post"
                      },
                    ),
                  ]),
                ),
                @tactics.repeat_tac(@tactics.strip_tac),
                subst_vars(),
                @simp.rewrite_tac(ths([@lists.length()])),
                @tactics.try_tac(@tactics.conv_tac(@calc_num.num_reduce_conv)),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let cp = call_pre(p, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let cq = call_post(q, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let _ = lemma(
    prefix + "_all",
    page_quantify(
      envvars + exvars + [("vs0", "List[Value]"), ("lc0", "List[Value]")],
    ) +
    needs +
    " → sl_triple_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    cp +
    ",[Call(" +
    idx +
    ")]," +
    cq +
    ",NIL)",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_triple_m_of_g")),
        @tactics.exists_tac(tm(spec)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_apply(
              inst(specs, envvars.map(x => "(" + x.0 + " : " + x.1 + ")")),
            ),
            seq([
              @logic.match_mp_tac(thm("sl_call_g")),
              @simp.rewrite_tac(ths([@class.eta_ax()])),
              @tactics.match_accept_tac(
                @simp.rewrite_rule(ths([@class.eta_ax()]))(call),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
