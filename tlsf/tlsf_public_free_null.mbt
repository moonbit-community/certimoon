// A null pointer branches out before loading any allocation header.

///|
fn prove_tlsf_public_free_null() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let fp = "(fp : " + rty + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_public_free_null_guard",
    "∀ d : " +
    w +
    ", val(d) <= 4294965088 → word_ult((word(0) : " +
    w +
    "),word_add(tlsf_base(d),word(2184)))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(inst(thm("tlsf_public_free_guard_value"), [a[0]])),
        arw([]),
        strip,
        arw([@words.word_ult_v1(), @words.val_word_0()]),
        @int.asm_arith_tac,
      ])
    },
  )
  let vars = malloc_g_variables() +
    [("pop", "Num"), ("push", "Num"), ("free_idx", "Num")] +
    page_model_variables() +
    [("l1", "Value"), ("l2", "Value"), ("fp", rty)]
  let r = malloc_frame(a, fp, "")
  let lc = "[" + malloc_i("word(0)") + ",(l1 : Value),(l2 : Value)]"
  let after = "st(NIL,[" +
    malloc_i("word(0)") +
    "," +
    malloc_i(a[0]) +
    ",(l2 : Value)]," +
    r +
    ")"
  let code = "tlsf_public_free_body(d,free_idx)"
  let afters = malloc_continuations(malloc_program_code(code)).map(instr => {
    if args_of(instr, "If", 3) is Some([_, yes, _]) &&
      @basics.dest_list(yes).length() == 1 &&
      head_name(@basics.dest_list(yes).head().unwrap()) == "Unreachable" {
      after
    } else {
      malloc_false()
    }
  })
  let _ = lemma(
    "tlsf_public_free_dead_dispatch",
    page_quantify(
      malloc_g_variables() + [("d", w), ("free_idx", "Num"), ("P", sassn)],
    ) +
    "F → sl_triple_g(" +
    malloc_g_env() +
    ",(P : " +
    sassn +
    "),tlsf_public_free_dispatch(d,free_idx)," +
    malloc_false() +
    ",(labels : List[" +
    sassn +
    "]))",
    () => seq([@tactics.repeat_tac(@tactics.strip_tac), small_meson(ths([]))]),
  )
  let path = sym_prove(
    "tlsf_public_free_null_path",
    page_quantify(vars) +
    "!word_ugt(" +
    a[0] +
    ",word(4294965088)) && word_ult((word(0) : " +
    w +
    "),word_add(tlsf_base(" +
    a[0] +
    "),word(2184))) → sl_triple_g(" +
    malloc_g_env() +
    ",st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    public_free_post(a, fp) +
    ",CONS(" +
    public_free_post(a, fp) +
    ",(labels : List[" +
    sassn +
    "])))",
    [],
    () => Array::make(3, public_free_final_vc()),
    afters~,
    chunks=[thm("tlsf_public_free_dead_dispatch")],
    rws=[thm("tlsf_base")],
    kind="lemma",
  )
  let _ = lemma(
    "tlsf_public_free_null_case",
    page_quantify(vars) +
    "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") → sl_triple_g(" +
    malloc_g_env() +
    ",st(NIL," +
    lc +
    "," +
    r +
    ")," +
    code +
    "," +
    public_free_post(a, fp) +
    ",CONS(" +
    public_free_post(a, fp) +
    ",(labels : List[" +
    sassn +
    "])))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_malloc_guard_facts"), a), g),
          )(g)
        },
        free_have(
          "val(" + a[0] + ") <= 4294965088",
          seq([
            @tactics.undisch_tac(
              tm("tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"),
            ),
            @simp.rewrite_tac(ths([thm("tlsf_physical_ok")])),
            small_meson(ths([])),
          ]),
        ),
        g => {
          @tactics.assume_tac(
            block_under(inst(thm("tlsf_public_free_null_guard"), [a[0]]), g),
          )(g)
        },
        free_apply(path),
      ])
    },
  )
}
