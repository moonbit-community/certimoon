// Keep the emitted shift as the call argument, while exposing a natural
// slot size and normalized caller locals in the result.

///|
fn prove_tlsf_malloc_page_shift_call() -> Unit raise {
  let a = block_model_args()
  let kw = "(kw : " + w32 + ")"
  let sn = "8*val(" + kw + ")"
  let shift = "word_jshl(" + kw + ",word(3))"
  let g = malloc_g_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
  let env = [
    ("pop", "Num"),
    ("push", "Num"),
    ("take_idx", "Num"),
    ("page_idx", "Num"),
  ]
  let vars = malloc_g_variables() +
    env +
    page_model_variables() +
    [
      ("kw", w32),
      ("before", heap),
      ("fp", rty),
      ("original", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  for v in malloc_variant_names() {
    let caller = malloc_locals(v, [
      malloc_i("word(0)"),
      malloc_i(kw),
      malloc_i(shift),
      "(l3 : Value)",
      "(l4 : Value)",
    ])
    let source = inst(
      thm("tlsf_malloc_page_oriented_call_g"),
      g +
      env.map(x => "(" + x.0 + " : " + x.1 + ")") +
      a +
      [sn, "(before : " + heap + ")", "(fp : " + rty + ")", caller],
    )
    let (need, tr) = @basics.dest_imp(@kernel.concl(source))
    let t = args_of(tr, "sl_triple_g", 9).unwrap()
    let pre = malloc_replace_term(
      t[5],
      tm("(word(" + sn + ") : " + w32 + ")"),
      tm(shift),
    )
    let post = malloc_replace_term(
      t[7],
      tm(shift),
      tm("(word(" + sn + ") : " + w32 + ")"),
    )
    let _ = lemma(
      "tlsf_malloc_" + v + "_page_shift_call_g",
      page_quantify(vars) +
      "val(" +
      kw +
      ") < 33 && (" +
      show(need) +
      ") → sl_triple_g(" +
      malloc_g_env() +
      "," +
      show(pre) +
      ",[Call(page_idx)]," +
      show(post) +
      ",(labels : List[" +
      sassn +
      "]))",
      () => {
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            @tactics.assume_tac(
              @simp.rewrite_rule(ths([@words.word_val()]))(
                block_under(
                  inst(thm("tlsf_malloc_small_shift"), ["val(" + kw + ")"]),
                  g,
                ),
              ),
            )(g)
          },
          g => {
            seq([
              @simp.asm_rewrite_tac(ths([])),
              free_apply(@simp.rewrite_rule(g.0.map(x => x.1))(source)),
            ])(g)
          },
        ])
      },
    )
  }
}
