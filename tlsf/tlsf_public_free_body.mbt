// Close the outer unit block and relate allocation handles to the three paths.

///|
fn prove_tlsf_public_free_body() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let ptr = "(ptr : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let l1 = "(l1 : Value)"
  let l2 = "(l2 : Value)"
  let q = public_free_post(a, fp)
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let label = lemma(
    "tlsf_public_free_label",
    page_quantify(
      model +
      [
        ("fp", rty),
        ("vs", "List[Value]"),
        ("lc", "List[Value]"),
        ("gs", "List[Value]"),
        ("ms", "Num"),
        ("h", heap),
      ],
    ) +
    "(LENGTH((vs : List[Value])) == 0 && (" +
    q +
    ")(vs,(lc : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))) == (" +
    q +
    ")(vs,lc,gs,ms,h)",
    () => {
      seq([
        gen,
        beta_goal(),
        @class.asm_cases_tac(tm("(vs : List[Value]) == NIL")),
        arw([@lists.length()]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
      ])
    },
  )
  let envvars = [("pop", "Num"), ("push", "Num"), ("free_idx", "Num")]
  let vars = malloc_g_variables() +
    envvars +
    model +
    [("ptr", w), ("l1", "Value"), ("l2", "Value"), ("fp", rty)]
  let natives = block_native_hyp()
  let wrapped = lemma(
    "tlsf_public_free_wrapped_cases",
    page_quantify(vars) +
    natives +
    " → sl_triple_g(" +
    malloc_g_env() +
    "," +
    public_free_cases(a, ptr, l1, l2, fp) +
    ",tlsf_public_free_code(d,free_idx)," +
    q +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        gen,
        strip,
        @simp.pure_rewrite_tac(ths([thm("tlsf_public_free_code")])),
        free_intro(),
        @tactics.conv_tac(pre_conv(norm_conv())),
        free_at(
          "public wrapper: outer block",
          @logic.match_mp_tac(thm("sl_block_st_g")),
        ),
        beta_goal(),
        @tactics.conv_tac(
          norm_conv(extra=[@equal.beta_rule(label), thm("tbv_results")]),
        ),
        free_at(
          "public wrapper: selected path",
          @tactics.first(
            @list.List(
              ["null", "large", "small"].map(which => {
                solve(g => {
                  let path = @equal.conv_rule(
                    norm_conv(),
                    @simp.pure_rewrite_rule(ths([thm("tlsf_public_free_body")]))(
                      thm("tlsf_public_free_" + which + "_case"),
                    ),
                  )
                  free_apply(path)(g)
                })
              }),
            ),
          ),
        ),
      ])
    },
  )
  let zero = malloc_i("word(0)")
  let pfn = "tlsf_public_free_pre(" + (a + [ptr, fp]).join(",") + ")"
  let qfn = "tlsf_public_free_post(" + [a[0], a[1], fp].join(",") + ")"
  let bp = body_pre(pfn, "(args : List[Value])", "[" + zero + "," + zero + "]")
  let bq = body_post(qfn)
  let source = inst(
    wrapped,
    [
      "(G : " + malloc_g_variables()[0].1 + ")",
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      bq,
      "[" + bq + "]",
      "(pop : Num)",
      "(push : Num)",
      "(free_idx : Num)",
    ] +
    a +
    [ptr, zero, zero, fp],
  )
  let _ = lemma(
    "tlsf_public_free_native_body",
    page_quantify(
      malloc_g_variables()[:4].to_owned() +
      envvars +
      model +
      [("ptr", w), ("fp", rty), ("args", "List[Value]")],
    ) +
    natives +
    " → sl_triple_g((G : " +
    malloc_g_variables()[0].1 +
    "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    bq +
    "," +
    bp +
    ",tlsf_public_free_code(d,free_idx)," +
    bq +
    ",[" +
    bq +
    "])",
    () => {
      seq([
        gen,
        strip,
        free_g_conseq(
          source,
          seq([
            gen,
            beta_goal(),
            strip,
            free_have(
              "(args : List[Value]) == [" + malloc_i(ptr) + "]",
              seq([
                @tactics.undisch_tac(
                  tm(
                    pfn +
                    "((args : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
                    heap +
                    "))",
                  ),
                ),
                rw([thm("tlsf_public_free_pre")]),
                small_meson(ths([])),
              ]),
            ),
            subst_only("args"),
            free_apply(
              inst(
                thm("tlsf_public_free_entry_cases"),
                a +
                [
                  ptr,
                  zero,
                  zero,
                  fp,
                  "(vs : List[Value])",
                  "(lc : List[Value])",
                  "(gs : List[Value])",
                  "(ms : Num)",
                  "(h : " + heap + ")",
                ],
              ),
            ),
            beta_goal(),
            arw([@lists.append()]),
          ]),
          seq([
            gen,
            beta_goal(),
            rw([thm("tlsf_public_free_post")]),
            strip,
            arw([]),
          ]),
        ),
      ])
    },
  )
}
