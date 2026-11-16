///|
fn prove_tlsf_block_free_list_members() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let last = lemma(
    "tlsf_small_last_member",
    "∀ xs : \{lw}, !(xs == NIL) → MEM(tlsf_small_last((word(0) : \{w}),xs),xs)",
    seq([
      @lists.list_induct_tac,
      rw([
        @lists.not_cons_nil(),
        thm("tlsf_small_last"),
        @lists.last(),
        @lists.mem(),
      ]),
      @class.cond_cases_tac,
      arw([@lists.mem()]),
      @tactics.first_x_assum(th => {
        if @basics.is_imp(@kernel.concl(th)) {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw([thm("tlsf_small_last")]),
      small_meson(ths([])),
    ]),
  )
  let _ = last
}

///|
fn block_returned_post(
  eqs : Array[@kernel.Thm],
  params : Array[String],
) -> @tactics.Tactic raise {
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    beta_goal(),
    @simp.rewrite_tac(ths([@lists.append()] + lift_rws())),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    g => {
      let all = @basics.strip_comb(g.1).1.to_array()
      guard head_name(g.1) == "tlsf_block_free_post" && all.length() == 25 else {
        raise Failure("block_returned_post: expected allocator post")
      }
      let fold = @simp.rewrite_rule(ths(eqs + [@lists.append()]))(
        inst(
          thm("tlsf_block_free_post_returned"),
          params + all[20:].to_owned().map(show),
        ),
      )
      free_apply(fold)(g)
    },
  ])
}
