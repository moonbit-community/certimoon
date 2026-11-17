///|
fn malloc_g_variables() -> Array[(String, String)] {
  let ft = "(List[Value],List[Value],Num," + heap + ") -> Bool"
  [
    ("G", "(Num," + ft + "," + ft + ") -> Bool"),
    ("fs", "List[Cl]"),
    ("tabs", "List[(Tab_t,List[V_ref])]"),
    ("inst", "Inst"),
    ("rp", sassn),
    ("labels", "List[" + sassn + "]"),
  ]
}

///|
fn malloc_g_env() -> String {
  page_arguments(malloc_g_variables()[:5].to_owned())
}

///|
fn prove_tlsf_malloc_dead_initialize() -> Unit raise {
  let _ = lemma(
    "tlsf_malloc_dead_initialize",
    page_quantify(
      malloc_g_variables() + [("P", sassn), ("initialize_idx", "Num")],
    ) +
    "F → sl_triple_g(" +
    malloc_g_env() +
    ",(P : " +
    sassn +
    "),[Call(initialize_idx)]," +
    "((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => F)" +
    ",(labels : List[" +
    sassn +
    "]))",
    () => seq([@tactics.repeat_tac(@tactics.strip_tac), small_meson(ths([]))]),
  )
}

///|
fn prove_tlsf_malloc_ready_raw() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let slot = "word_add(word_and(word_add(" +
    a[0] +
    ",word(15)),word(4294967280)),word(1908))"
  let lc = (l1 : String) => {
    malloc_locals("try", [
      malloc_i(n),
      malloc_i(l1),
      "(l2 : Value)",
      "(l3 : Value)",
      "(l4 : Value)",
    ])
  }
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let cond = "!word_ugt(" +
    a[0] +
    ",word(4294965088)) && !word_uge(word_jushr(" +
    slot +
    ",word(16)),(word(DIV(" +
    a[1] +
    ",65536)) : " +
    w +
    ")) && !(" +
    a[2] +
    " == word(0))"
  let vars = malloc_g_variables() +
    malloc_publication_variables() +
    page_model_variables() +
    [
      ("l0", "Value"),
      ("n", w),
      ("before", heap),
      ("fp", rty),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths([thm("tlsf_malloc_ro")])),
    @tactics.try_tac(small_meson(ths([]))),
  ])
  for v in malloc_variant_names() {
    let locals_for = (l1 : String) => {
      malloc_locals(
        v,
        if v == "first" {
          [l1, "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)"]
        } else {
          [malloc_i(n), l1, "(l2 : Value)", "(l3 : Value)", "(l4 : Value)"]
        },
      )
    }
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_ready_raw",
        page_quantify(vars) +
        cond +
        " → sl_triple_g(" +
        malloc_g_env() +
        ",st(NIL," +
        locals_for(if v == "first" { "(l0 : Value)" } else { "(l1 : Value)" }) +
        "," +
        r +
        ")," +
        malloc_part(v, "ready_guard") +
        ",st(NIL," +
        locals_for(malloc_i(slot)) +
        "," +
        r +
        "),(labels : List[" +
        sassn +
        "]))",
        [],
        () => Array::make(2, same),
        afters=[
          "st(NIL," + locals_for(malloc_i(a[0])) + "," + r + ")",
          "st([" +
          malloc_i(a[2]) +
          "]," +
          locals_for(malloc_i(slot)) +
          "," +
          r +
          ")",
        ],
        rules=step_rules + ["st_malloc_load_top", "st_malloc_memory_size"],
        chunks=[thm("tlsf_malloc_dead_initialize")],
        kind="lemma",
      ),
    )
  }
  let _ = lc
}
