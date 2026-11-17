// Both dispatch arms invoke already checked compiled allocator code.

///|
fn prove_tlsf_public_free_branches() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let g = malloc_g_variables().map(v => "(" + v.0 + " : " + v.1 + ")")
  let envvars = [("pop", "Num"), ("push", "Num"), ("free_idx", "Num")]
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let m = "(m : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let lc = "(caller : List[Value])"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let natives = block_native_hyp()
  let back = block_backing(a)
  let source = inst(
    thm("tlsf_small_return_all"),
    [
      "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)", "(pop : Num)",
      "(push : Num)", "(free_idx : Num)",
    ] +
    a +
    [m, fp, "(NIL : List[Value])", lc],
  )
  let cap = "val(tlsf_size(" + a[4] + "(" + m + ")))"
  let pre = "st([" +
    malloc_i(m) +
    "]," +
    lc +
    "," +
    public_free_r(a, m, cap, fp) +
    ")"
  let post = "st([" +
    malloc_i("word(0)") +
    "]," +
    lc +
    "," +
    public_free_state(a, fp) +
    ")"
  let cond = back +
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
    natives
  let vs = envvars + model + [("m", w), ("fp", rty), ("caller", "List[Value]")]
  let ordinary = lemma(
    "tlsf_public_free_large_call",
    page_quantify(malloc_g_variables()[1:4].to_owned() + vs) +
    cond +
    " → sl_triple_m(" +
    env +
    "," +
    pre +
    ",[Call(free_idx)]," +
    post +
    ",NIL)",
    () => {
      seq([
        gen,
        strip,
        initialize_m_conseq(
          source,
          ent_tac(
            [thm("tlsf_free_pre"), thm("tlsf_allocator_frame"), @lists.append()],
            [],
          ),
          seq([
            gen,
            beta_goal(),
            rw([@lists.append(), thm("tlsf_small_return_post"), thm("st")]),
            strip,
            subst_vars(),
            arw([]),
            public_free_fold(),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_public_free_large_call_g",
    page_quantify(malloc_g_variables() + vs) +
    cond +
    " → sl_triple_g(" +
    malloc_g_env() +
    "," +
    pre +
    ",[Call(free_idx)]," +
    post +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        gen,
        strip,
        free_lift(
          inst(
            ordinary,
            g[1:4].to_owned() +
            ["(pop : Num)", "(push : Num)", "(free_idx : Num)"] +
            a +
            [m, fp, lc],
          ),
        ),
      ])
    },
  )
  let smallsource = inst(
    thm("tlsf_block_free_body"),
    g[:4].to_owned() +
    ["(pop : Num)", "(push : Num)", "(free_idx : Num)"] +
    g[4:].to_owned() +
    a +
    [p, b, malloc_i("word_add(" + b + ",word(8))"), "(l2 : Value)", fp],
  )
  let smallpre = "st(NIL,[" +
    malloc_i("word_add(" + b + ",word(8))") +
    "," +
    malloc_i(b) +
    ",(l2 : Value)]," +
    public_free_r(a, b, a[9] + "(" + p + ")", fp) +
    ")"
  let _ = lemma(
    "tlsf_public_free_small_branch",
    page_quantify(
      malloc_g_variables() +
      envvars +
      model +
      [("p", w), ("b", w), ("l2", "Value"), ("fp", rty)],
    ) +
    "MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    b +
    "," +
    a[12] +
    "(" +
    p +
    ")) && " +
    natives +
    " → sl_triple_g(" +
    malloc_g_env() +
    "," +
    smallpre +
    ",tlsf_block_free_code(d,free_idx)," +
    public_free_result(a, fp) +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        gen,
        strip,
        free_g_conseq(
          smallsource,
          ent_tac([thm("tlsf_block_free_pre")], []),
          seq([
            gen,
            beta_goal(),
            rw([thm("tlsf_block_free_post")]),
            strip,
            subst_vars(),
            @tactics.exists_tac(tm("(lc : List[Value])")),
            rw([thm("st")]),
            arw([]),
            public_free_fold(),
          ]),
        ),
      ])
    },
  )
}
