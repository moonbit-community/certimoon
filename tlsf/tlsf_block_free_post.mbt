// Fold either unchanged TLSF ownership or the closed reclamation post into
// the single allocator-level result contract.

///|
fn prove_tlsf_block_free_post() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let args = block_model_args()
  let params = page_arguments(vs)
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let updated = block_after_free(args, p, b)
  let q = "tlsf_block_free_post(" + params + ")"
  let state = block_rty(updated, "(fp : " + rty + ")")
  let u = "V_num(ConstInt32((word(0) : " + w + ")))"
  let suffix = "∀ res : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let old = block_backing(args) +
    " && " +
    block_lists(args) +
    " && MEM(" +
    p +
    "," +
    args[8] +
    ") && MEM(" +
    b +
    "," +
    args[12] +
    "(" +
    p +
    "))"
  let _ = lemma(
    "tlsf_block_free_post_same",
    page_quantify(vs) +
    suffix +
    ", " +
    old +
    " && (res : List[Value]) == [" +
    u +
    "] && (" +
    state +
    ")((gs : List[Value]),(ms : Num),(h : " +
    heap +
    ")) → " +
    q +
    "(res,lc,gs,ms,h)",
    seq([
      gen,
      beta_goal(),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(inst(thm("tlsf_block_free_models"), args + [p, b]), g),
        )(g)
      },
      rw([thm("tlsf_block_free_post")]),
      arw([]),
      seq([2, 3, 4, 5, 6, 7].map(i => @tactics.exists_tac(tm(args[i])))),
      rw([thm("tlsf_allocator_frame"), thm("tlsf_small")] + lift_rws()),
      arw([]),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(ac),
    ]),
  )
  let returned = "tlsf_small_return_post(" +
    (updated + [p, "(fp : " + rty + ")"]).join(",") +
    ")"
  let _ = lemma(
    "tlsf_block_free_post_returned",
    page_quantify(vs) +
    suffix +
    ", " +
    returned +
    "((res : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    ")) → " +
    q +
    "(res,lc,gs,ms,h)",
    rw([thm("tlsf_small_return_post"), thm("tlsf_block_free_post")]),
  )
}
