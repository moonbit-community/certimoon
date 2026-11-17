///|
fn prove_tlsf_malloc_result_frame() -> Unit raise {
  let w = w32
  let args = "(d : " +
    w +
    "),(n : " +
    w +
    "),(lim : Num),(fp : " +
    rty +
    "),(ptr : " +
    w +
    ")"
  let vars = "∀ d : " +
    w +
    ", ∀ n : " +
    w +
    ", ∀ lim : Num, ∀ fp : " +
    rty +
    ", ∀ ptr : " +
    w +
    ", ∀ gs : List[Value], ∀ ms : Num, ∀ h : " +
    heap +
    ", "
  let _ = lemma(
    "tlsf_malloc_result_pointer",
    vars +
    "tlsf_malloc_result(" +
    args +
    ")(gs,ms,h) → !(ptr == word(0)) && !(ptr == word(4294967295))",
    seq([
      @simp.rewrite_tac(ths([thm("tlsf_malloc_result")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      page_publish_atomic([]),
    ]),
  )
  let frame = "(gs : List[Value]) => (ms : Num) => (fp : " +
    rty +
    ")(gs,(lim : Num))"
  let _ = lemma(
    "tlsf_malloc_result_original_frame",
    vars +
    "∀ next : Num, lim <= next && tlsf_malloc_result((d : " +
    w +
    "),(n : " +
    w +
    "),next," +
    frame +
    ",(ptr : " +
    w +
    "))(gs,ms,h) → tlsf_malloc_result(" +
    args +
    ")(gs,ms,h)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("tlsf_malloc_result")])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      seq(
        (page_model_variables()[2:].to_owned() + [("cap", "Num")]).map(x => {
          @tactics.exists_tac(tm("(" + x.0 + " : " + x.1 + ")"))
        }),
      ),
      @simp.asm_rewrite_tac(ths(malloc_ac())),
      @int.asm_arith_tac,
    ]),
  )
}
