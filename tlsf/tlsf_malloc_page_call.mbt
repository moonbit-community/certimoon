// Close the real Memory::take call, then expose its two allocator-level outcomes.

///|
fn prove_tlsf_malloc_page_call() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let n = "(s : " + w + ")"
  let before = "(before : " + heap + ")"
  let fp = "(fp : " + rty + ")"
  let lc = "(caller : List[Value])"
  let _sf = "(gs : List[Value]) => (ms : Num) => star(tlsf_small(" +
    [a[0], a[4], a[8], a[9], a[10], a[11], a[12], a[13], a[14]].join(",") +
    "),(" +
    fp +
    ")(gs,ms))"
  let envvars = [
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("pop", "Num"),
    ("push", "Num"),
    ("take_idx", "Num"),
    ("page_idx", "Num"),
  ]
  let env = envvars.map(x => "(" + x.0 + " : " + x.1 + ")")
  let source = inst(
    thm("tlsf_malloc_page_all"),
    env[:3].to_owned() +
    [a[0], env[3], env[4], env[5], env[6]] +
    a[1:].to_owned() +
    [n, before, fp, "(NIL : List[Value])", lc],
  )
  let natives = show(@basics.dest_imp(@kernel.concl(source)).0)
  let r = "tlsf_malloc_ro(" + (a + [before, fp]).join(",") + ")"
  let pre = "st([" + malloc_i(n) + "]," + lc + "," + r + ")"
  let post = "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => lc == " +
    lc +
    " && tlsf_malloc_page_ready_post(" +
    (a + [n, before, fp]).join(",") +
    ")(res,gs,ms,h)"
  let vars = envvars +
    model +
    [("s", w), ("before", heap), ("fp", rty), ("caller", "List[Value]")]
  let cond = "8 <= val(" +
    n +
    ") && val(" +
    n +
    ") <= 256 && MOD(val(" +
    n +
    "),8) == 0 && " +
    natives
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ordinary = lemma(
    "tlsf_malloc_page_call",
    page_quantify(vars) +
    cond +
    " → sl_triple_m(" +
    env[:3].to_owned().join(",") +
    "," +
    pre +
    ",[Call(page_idx)]," +
    post +
    ",NIL)",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        initialize_m_conseq(
          source,
          ent_tac(
            [
              thm("tlsf_malloc_page_pre"),
              thm("tlsf_malloc_ro"),
              @lists.append(),
            ],
            [],
          ),
          seq([
            gen,
            beta_goal(),
            rw([@lists.append()]),
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            arw([]),
            g => {
              free_apply(
                @simp.rewrite_rule(g.0.map(x => x.1))(
                  inst(
                    thm("tlsf_malloc_page_expand"),
                    a +
                    [
                      n,
                      before,
                      fp,
                      "(vs : List[Value])",
                      "(gs : List[Value])",
                      "(ms : Num)",
                      "(h : " + heap + ")",
                    ],
                  ),
                ),
              )(g)
            },
          ]),
        ),
      ])
    },
  )
  let flat = @equal.rhs(
    @kernel.concl(
      @simp.rewrite_conv(ths([thm("tlsf_malloc_page_ready_post")]))(tm(post)),
    ),
  )
  let _ = lemma(
    "tlsf_malloc_page_call_g",
    page_quantify(
      malloc_g_variables() +
      envvars[3:].to_owned() +
      model +
      [("s", w), ("before", heap), ("fp", rty), ("caller", "List[Value]")],
    ) +
    cond +
    " → sl_triple_g(" +
    malloc_g_env() +
    "," +
    pre +
    ",[Call(page_idx)]," +
    show(flat) +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_lift(
          @simp.rewrite_rule(ths([thm("tlsf_malloc_page_ready_post")]))(
            inst(ordinary, env + a + [n, before, fp, lc]),
          ),
        ),
      ])
    },
  )
  let _ = arw
}
