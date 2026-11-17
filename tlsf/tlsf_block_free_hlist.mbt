// A commutative fold lets page and slot ownership be focused without fixing
// their order in the abstract lists.

///|
fn define_tlsf_block_free_hlist() -> Unit raise {
  def(
    "tlsf_small_hlist",
    "tlsf_small_hlist((ff : (\{w32}) -> \{hprop}),(NIL : List[\{w32}])) == emp && tlsf_small_hlist(ff,CONS((p : \{w32}),ps)) == star(ff(p),tlsf_small_hlist(ff,ps))",
  )
}

///|
fn prove_tlsf_block_free_hlist() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ft = "(\{w}) -> \{hprop}"
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_small_hlist_append",
    "∀ xs : \{lw}, ∀ ff : \{ft}, ∀ ys : \{lw}, tlsf_small_hlist(ff,APPEND(xs,ys)) == star(tlsf_small_hlist(ff,xs),tlsf_small_hlist(ff,ys))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([@lists.append(), thm("tlsf_small_hlist")] + ac),
        gen,
        arw(ac),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_hlist_cong",
    "∀ xs : \{lw}, ∀ ff : \{ft}, ∀ gg : \{ft}, (∀ p : \{w}, MEM(p,xs) → ff(p) == gg(p)) → tlsf_small_hlist(ff,xs) == tlsf_small_hlist(gg,xs)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_small_hlist"), @lists.mem()]),
        gen,
        strip,
        free_have(
          "(ff : \{ft})((h : \{w})) == (gg : \{ft})(h)",
          small_meson(ths([])),
        ),
        arw([]),
        @tactics.ap_term_tac,
        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
        small_meson(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_hlist_focus",
    "∀ xs : \{lw}, ∀ ff : \{ft}, ∀ p : \{w}, tlsf_count(p,xs) == 1 → tlsf_small_hlist(ff,xs) == star(ff(p),tlsf_small_hlist(ff,tlsf_small_remove(p,xs)))",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "MEM((p : \{w}),(xs : \{lw}))",
          seq([rw([thm("tlsf_count_member")]), @int.asm_arith_tac]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_small_member_split"), [
            "(p : " + w + ")",
            "(xs : " + lw + ")",
          ]),
        ),
        arw([]),
        strip,
        subst_vars(),
        @tactics.mp_tac(
          inst(thm("tlsf_small_count_one_split"), [
            "(a : " + lw + ")",
            "(z : " + lw + ")",
            "(p : " + w + ")",
          ]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_small_remove_split"), [
            "(a : " + lw + ")",
            "(z : " + lw + ")",
            "(p : " + w + ")",
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        arw([thm("tlsf_small_hlist_append"), thm("tlsf_small_hlist")] + ac),
      ])
    },
  )
}
