// Dual to dtail: dhead omits the first node's previous link, so unlinking
// can expose both neighbours while retaining all interior links unchanged.

///|
fn define_tlsf_block_free_dhead() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  def(
    "tlsf_small_dhead",
    "tlsf_small_dhead((NIL : \{lw}),(nx : \{w})) == emp && tlsf_small_dhead(CONS((p : \{w}),ps),nx) == star(pts(val(p)+28,serialise_i32(tlsf_small_first(ps,nx))),tlsf_small_dlist(p,ps,nx))",
  )
}

///|
fn prove_tlsf_block_free_dhead() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_small_dlist_head",
    "∀ xs : \{lw}, ∀ pr : \{w}, ∀ nx : \{w}, tlsf_small_dlist(pr,xs,nx) == star((if xs == NIL { emp } else { pts(val(HD(xs))+24,serialise_i32(pr)) }),tlsf_small_dhead(xs,nx))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_small_dlist_nil"), thm("tlsf_small_dhead")] + ac),
        gen,
        rw([
          thm("tlsf_small_dlist_cons"),
          thm("tlsf_small_dhead"),
          @lists.not_cons_nil(),
          @lists.hd(),
        ]),
      ])
    },
  )
  let pr = "tlsf_small_last((prev : \{w}),(a : \{lw}))"
  let nx = "tlsf_small_first((z : \{lw}),(next : \{w}))"
  let target = small_star([
    "tlsf_small_dtail((prev : \{w}),(a : \{lw}))",
    "if (a : \{lw}) == NIL { emp } else { pts(val(\{pr})+28,serialise_i32((p : \{w}))) }",
    "pts(val((p : \{w}))+24,serialise_i32(\{pr}))",
    "pts(val((p : \{w}))+28,serialise_i32(\{nx}))",
    "if (z : \{lw}) == NIL { emp } else { pts(val(HD(z))+24,serialise_i32((p : \{w}))) }",
    "tlsf_small_dhead((z : \{lw}),(next : \{w}))",
  ])
  let _ = lemma(
    "tlsf_small_dlist_unlink_view",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ prev : \{w}, ∀ next : \{w}, ∀ p : \{w}, tlsf_small_dlist(prev,APPEND(a,CONS(p,z)),next) == \{target}",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_small_dlist_append"),
          thm("tlsf_small_dlist_cons"),
          thm("tlsf_small_first"),
          @lists.not_cons_nil(),
          @lists.hd(),
        ]),
        @tactics.conv_tac(
          @equal.subs_conv(
            ths([
              inst(thm("tlsf_small_dlist_tail"), [
                "(a : " + lw + ")",
                "(prev : " + w + ")",
                "(p : " + w + ")",
              ]),
              inst(thm("tlsf_small_dlist_head"), [
                "(z : " + lw + ")",
                "(p : " + w + ")",
                "(next : " + w + ")",
              ]),
            ]),
          ),
        ),
        rw(ac),
      ])
    },
  )
  let target2 = small_star([
    "tlsf_small_dtail((prev : \{w}),(a : \{lw}))",
    "if (a : \{lw}) == NIL { emp } else { pts(val(\{pr})+28,serialise_i32(\{nx})) }",
    "if (z : \{lw}) == NIL { emp } else { pts(val(HD(z))+24,serialise_i32(\{pr})) }",
    "tlsf_small_dhead((z : \{lw}),(next : \{w}))",
  ])
  let _ = lemma(
    "tlsf_small_dlist_removed_view",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ prev : \{w}, ∀ next : \{w}, tlsf_small_dlist(prev,APPEND(a,z),next) == \{target2}",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_dlist_append")]),
        @tactics.conv_tac(
          @equal.subs_conv(
            ths([
              inst(thm("tlsf_small_dlist_tail"), [
                "(a : " + lw + ")",
                "(prev : " + w + ")",
                nx,
              ]),
              inst(thm("tlsf_small_dlist_head"), [
                "(z : " + lw + ")",
                pr,
                "(next : " + w + ")",
              ]),
            ]),
          ),
        ),
        rw(ac),
      ])
    },
  )
}
