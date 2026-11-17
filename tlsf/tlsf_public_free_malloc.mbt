// A successful allocation supplies precisely the ownership consumed by free.
// Keep an old client frame fixed at its allocation-time memory length.

///|
fn prove_tlsf_public_free_malloc() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let a = block_model_args()
  let current = a.copy()
  current[1] = "(ms : Num)"
  let fp = "(fp : " + rty + ")"
  let ptr = "(ptr : " + w + ")"
  let frame = "(gs0 : List[Value]) => (ms0 : Num) => " +
    fp +
    "(gs0,(oldlim : Num))"
  let pre = "tlsf_public_free_pre(" +
    (current + [ptr, frame]).join(",") +
    ")([" +
    malloc_i(ptr) +
    "],(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))"
  let ex = model[2:]
    .to_owned()
    .map(v => "∃ " + v.0 + " : " + v.1 + ", ")
    .join("")
  let _ = lemma(
    "tlsf_public_free_malloc_result",
    page_quantify([
      ("d", w),
      ("n", w),
      ("oldlim", "Num"),
      ("fp", rty),
      ("ptr", w),
      ("gs", "List[Value]"),
      ("ms", "Num"),
      ("h", heap),
    ]) +
    "tlsf_malloc_result(" +
    [a[0], "(n : " + w + ")", "(oldlim : Num)", fp, ptr].join(",") +
    ")((gs : List[Value]),(ms : Num),(h : " +
    heap +
    ")) → (" +
    ex +
    pre +
    ")",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(ths([thm("tlsf_malloc_result")])),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        seq(a[2:].to_owned().map(x => @tactics.exists_tac(tm(x)))),
        @simp.rewrite_tac(ths([thm("tlsf_public_free_pre")])),
        @simp.asm_rewrite_tac(ths([])),
        @tactics.exists_tac(tm("(cap : Num)")),
        @simp.asm_rewrite_tac(ths([])),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        @simp.asm_rewrite_tac(ths(malloc_ac())),
      ])
    },
  )
}
