// The exported unit-returning native free closure, with real helper closures.

///|
fn public_free_env_variables() -> Array[(String, String)] {
  [
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("pop", "Num"),
    ("push", "Num"),
    ("free_idx", "Num"),
    ("public_idx", "Num"),
  ]
}

///|
fn prove_tlsf_public_free_module() -> Unit raise {
  let w = w32
  let ft = "(List[Value],List[Value],Num," + heap + ") -> Bool"
  let envvars = public_free_env_variables()
  let env = envvars.map(v => "(" + v.0 + " : " + v.1 + ")")
  let a = block_model_args()
  let model = page_model_variables()
  let vs = model + [("ptr", w), ("fp", rty)]
  let params = page_arguments(vs)
  let p = "tlsf_public_free_pre(" + params + ")"
  let q = "tlsf_public_free_post(" +
    [a[0], a[1], "(fp : " + rty + ")"].join(",") +
    ")"
  let spec = "tlsf_public_free_spec((inst : Inst),(d : " +
    w +
    "),(free_idx : Num),(public_idx : Num))"
  let exvars = vs.filter(v => v.0 != "d")
  public_free_def(
    "tlsf_public_free_spec",
    spec +
    "((j : Num),(P : " +
    ft +
    "),(Q : " +
    ft +
    ")) == (j == sfunc_ind(inst,public_idx) && (" +
    exvars.map(v => "∃ " + v.0 + " : " + v.1 + ", ").join("") +
    "P == " +
    p +
    " && Q == " +
    q +
    "))",
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let call = lemma(
    "tlsf_public_free_spec_call",
    page_quantify(envvars + vs.filter(v => v.0 != "d") + [("d", w)]) +
    spec +
    "(sfunc_ind(inst,public_idx)," +
    p +
    "," +
    q +
    ")",
    () => {
      seq([
        gen,
        rw([thm("tlsf_public_free_spec")]),
        seq(
          exvars.map(v => @tactics.exists_tac(tm("(" + v.0 + " : " + v.1 + ")"))),
        ),
        rw([]),
      ])
    },
  )
  let ts = "[T_num(T_i32),T_num(T_i32)]"
  let zs = "[" + Array::make(2, malloc_i("word(0)")).join(",") + "]"
  let native = "EL(sfunc_ind((inst : Inst),(public_idx : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL)," +
    ts +
    ",tlsf_public_free_code((d : " +
    w +
    "),(free_idx : Num)))"
  let hyp = native + " && " + block_native_hyp()
  let specs = lemma(
    "tlsf_public_free_specs",
    page_quantify(envvars + [("d", w)]) +
    hyp +
    " → (∀ k : Num, specs_ok(k," +
    spec +
    ",fs,tabs,inst))",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_funs_g")),
        gen,
        rw([thm("tlsf_public_free_spec")]),
        strip,
        subst_vars(),
        seq(
          [
            "[T_num(T_i32)]",
            "(NIL : List[Valtype])",
            ts,
            "tlsf_public_free_code((d : " + w + "),(free_idx : Num))",
            zs,
          ].map(x => @tactics.exists_tac(tm(x))),
        ),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(arw([])),
            solve(
              rw([
                @wasm.thm("n_zeros"),
                @wasm.thm("bitzero"),
                @wasm.thm("bitzero_num"),
                @wasm.thm("map_option"),
                @lists.map(),
                @wasm.thm("those"),
              ]),
            ),
            solve(
              seq([
                gen,
                free_apply(
                  inst(
                    thm("tlsf_public_free_native_body"),
                    [spec] +
                    env[:3].to_owned() +
                    env[3:6].to_owned() +
                    a +
                    [
                      "(ptr : " + w + ")",
                      "(fp : " + rty + ")",
                      "(args : List[Value])",
                    ],
                  ),
                ),
              ]),
            ),
            solve(
              seq([
                gen,
                rw([thm("tlsf_public_free_pre"), thm("tlsf_public_free_post")]),
                @tactics.repeat_tac(@tactics.strip_tac),
                subst_vars(),
                rw([@lists.length()]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let cp = call_pre(p, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let cq = call_post(q, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let all = lemma(
    "tlsf_public_free_all",
    page_quantify(
      envvars + vs + [("vs0", "List[Value]"), ("lc0", "List[Value]")],
    ) +
    hyp +
    " → sl_triple_m(" +
    env[:3].to_owned().join(",") +
    "," +
    cp +
    ",[Call(public_idx)]," +
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
            free_apply(inst(specs, env + [a[0]])),
            seq([
              @logic.match_mp_tac(thm("sl_call_g")),
              rw([@class.eta_ax()]),
              @tactics.match_accept_tac(
                @simp.rewrite_rule(ths([@class.eta_ax()]))(call),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
  let runvars = [
    ("fr", hprop),
    ("s", "Wstore"),
    ("f", "Wframe"),
    ("vs", "List[Value]"),
    ("s2", "Wstore"),
    ("f2", "Wframe"),
    ("es2", "List[Einstr]"),
  ]
  let source = inst(
    all,
    env +
    vs.map(v => "(" + v.0 + " : " + v.1 + ")") +
    ["(vs0 : List[Value])", "(lc0 : List[Value])"],
  )
  let conclusion = args_of(
    @basics.dest_imp(@kernel.concl(source)).1,
    "sl_triple_m",
    7,
  ).unwrap()
  let adequate = @bool.ispecl(
    @list.List(
      conclusion[:6].to_owned() +
      runvars.map(v => tm("(" + v.0 + " : " + v.1 + ")")),
    ),
    thm("sl_triple_m_adequate"),
  )
  let (need, result) = @basics.dest_imp(@kernel.concl(adequate))
  let pre = ([@basics.dest_imp(@kernel.concl(source)).0] +
    @basics.conjuncts(need).to_array()[1:].to_owned())
    .map(t => "(" + show(t) + ")")
    .join(" && ")
  let _ = lemma(
    "tlsf_public_free_run",
    page_quantify(
      envvars + vs + [("vs0", "List[Value]"), ("lc0", "List[Value]")] + runvars,
    ) +
    pre +
    " → " +
    show(result),
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(adequate),
        arw([@class.eta_ax()]),
        free_apply(source),
      ])
    },
  )
}
