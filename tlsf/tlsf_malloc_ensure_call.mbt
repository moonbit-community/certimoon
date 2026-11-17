///|
fn malloc_ensure_call_post(a : Array[String], caller : String) -> String {
  let _w = w32
  let fp = "(fp : " + rty + ")"
  let newer = malloc_fresh_args(a)
  newer[1] = "(lim2 : Num)"
  let choices = [("lim2", "Num"), ("before2", heap)] +
    page_model_variables()[2:8].to_owned().map(x => (x.0 + "2", x.1))
  let frame = "(gs : List[Value]) => (ms : Num) => (" +
    fp +
    ")(gs," +
    a[1] +
    ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", fp]).join(",") +
    ")"
  let r2 = "tlsf_malloc_ro(" +
    (newer + ["(before2 : " + heap + ")", frame]).join(",") +
    ")"
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => st([" +
  malloc_i("word(0)") +
  "]," +
  caller +
  "," +
  r +
  ")(vs,lc,gs,ms,h) || (" +
  choices.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("") +
  a[1] +
  " <= (lim2 : Num) && st([" +
  malloc_i("word(1)") +
  "]," +
  caller +
  "," +
  r2 +
  ")(vs,lc,gs,ms,h))"
}

///|
fn prove_tlsf_malloc_ensure_call() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let caller = "(caller : List[Value])"
  let before = "(before : " + heap + ")"
  let sf = "(gs : List[Value]) => (ms : Num) => star(tlsf_small(" +
    [a[0], a[4], a[8], a[9], a[10], a[11], a[12], a[13], a[14]].join(",") +
    "),(" +
    fp +
    ")(gs,ms))"
  let env = [
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("pop", "Num"),
    ("push", "Num"),
    ("ensure_idx", "Num"),
  ]
  let es = env.map(x => "(" + x.0 + " : " + x.1 + ")")
  let source = inst(
    thm("tlsf_ensure_all"),
    es[:3].to_owned() +
    [a[0]] +
    es[3:].to_owned() +
    [n] +
    a[1:8].to_owned() +
    [before, sf, "(NIL : List[Value])", caller],
  )
  let natives = show(@basics.dest_imp(@kernel.concl(source)).0)
  let r = "tlsf_malloc_ro(" + (a + [before, fp]).join(",") + ")"
  let vars = env +
    page_model_variables() +
    [("n", w), ("before", heap), ("fp", rty), ("caller", "List[Value]")]
  let cond = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && 16 <= val(" +
    n +
    ") && val(" +
    n +
    ") <= 4160749568 && (" +
    natives +
    ")"
  let _ = lemma(
    "tlsf_malloc_ensure_call",
    page_quantify(vars) +
    cond +
    " → sl_triple_m(" +
    es[:3].to_owned().join(",") +
    ",st([" +
    malloc_i(n) +
    "]," +
    caller +
    "," +
    r +
    "),[Call(ensure_idx)]," +
    malloc_ensure_call_post(a, caller) +
    ",NIL)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      initialize_m_conseq(
        source,
        ent_tac(
          [
            thm("tlsf_ensure_pre"),
            thm("tlsf_malloc_ro"),
            thm("tlsf_allocator"),
            @lists.append(),
          ],
          [],
        ),
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          beta_goal(),
          @simp.rewrite_tac(ths([@lists.append()])),
          @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            @tactics.mp_tac(
              block_under(
                inst(
                  thm("tlsf_malloc_ensure_post_result"),
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
                g,
              ),
            )(g)
          },
          @simp.rewrite_tac(
            ths([
              thm("tlsf_malloc_ensure_post"),
              thm("st"),
              thm("tlsf_malloc_ro"),
            ]),
          ),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.try_tac(@tactics.disj2_tac),
          seq(
            (["(ms : Num)", "(h : " + heap + ")"] +
            malloc_fresh_args(a)[2:8].to_owned()).map(x => {
              @tactics.exists_tac(tm(x))
            }),
          ),
          @simp.asm_rewrite_tac(ths([])),
        ]),
      ),
    ]),
  )
}
