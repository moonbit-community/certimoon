// Terminal links are explicit so removing a partial page changes only its
// predecessor's next word, successor's previous word, or the table head.

///|
fn define_tlsf_block_free_dlist() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let cell = (b : String, k : Int32, v : String) => {
    "pts(val((\{b} : \{w}))+\{k},serialise_i32((\{v} : \{w})))"
  }
  def(
    "tlsf_small_dlist",
    "tlsf_small_dlist((pr : \{w}),(NIL : \{lw}),(nx : \{w})) == emp && tlsf_small_dlist(pr,CONS((p : \{w}),ps),nx) == star(\{cell("p",24,"pr")},star(\{cell("p",28,"if ps == NIL { nx } else { HD(ps) }")},tlsf_small_dlist(p,ps,nx)))",
  )
  def(
    "tlsf_small_last",
    "tlsf_small_last((fallback : \{w}),(xs : \{lw})) == (if xs == NIL { fallback } else { LAST(xs) })",
  )
  def(
    "tlsf_small_first",
    "tlsf_small_first((xs : \{lw}),(fallback : \{w})) == (if xs == NIL { fallback } else { HD(xs) })",
  )
  def(
    "tlsf_small_dtail",
    "tlsf_small_dtail((pr : \{w}),(NIL : \{lw})) == emp && tlsf_small_dtail(pr,CONS((p : \{w}),ps)) == star(\{cell("p",24,"pr")},(if ps == NIL { emp } else { star(\{cell("p",28,"HD(ps)")},tlsf_small_dtail(p,ps)) }))",
  )
}

///|
fn prove_tlsf_block_free_dlist() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
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
  let _ = lemma(
    "tlsf_small_partial_dlist",
    "∀ xs : \{lw}, ∀ pr : \{w}, tlsf_small_partial_links(pr,xs) == tlsf_small_dlist(pr,xs,word(0))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          thm("tlsf_small_partial_links"),
          thm("tlsf_small_dlist"),
          thm("tlsf_small_head"),
        ]),
        gen,
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_first_append",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ nx : \{w}, tlsf_small_first(APPEND(a,z),nx) == tlsf_small_first(a,tlsf_small_first(z,nx))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          thm("tlsf_small_first"),
          @lists.append(),
          @lists.not_cons_nil(),
          @lists.hd(),
        ]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_last_cons",
    "∀ p : \{w}, ∀ h : \{w}, ∀ t : \{lw}, tlsf_small_last(p,CONS(h,t)) == tlsf_small_last(h,t)",
    () => rw([thm("tlsf_small_last"), @lists.not_cons_nil(), @lists.last()]),
  )
  let _ = lemma(
    "tlsf_small_dlist_cons",
    "∀ pr : \{w}, ∀ p : \{w}, ∀ ps : \{lw}, ∀ nx : \{w}, tlsf_small_dlist(pr,CONS(p,ps),nx) == star(pts(val(p)+24,serialise_i32(pr)),star(pts(val(p)+28,serialise_i32(tlsf_small_first(ps,nx))),tlsf_small_dlist(p,ps,nx)))",
    () => rw([thm("tlsf_small_dlist"), thm("tlsf_small_first")]),
  )
  let nil = lemma(
    "tlsf_small_dlist_nil",
    "∀ pr : \{w}, ∀ nx : \{w}, tlsf_small_dlist(pr,(NIL : \{lw}),nx) == emp",
    () => rw([thm("tlsf_small_dlist")]),
  )
  let lastnil = lemma(
    "tlsf_small_last_nil",
    "∀ p : \{w}, tlsf_small_last(p,(NIL : \{lw})) == p",
    () => rw([thm("tlsf_small_last")]),
  )
  let _ = lemma(
    "tlsf_small_dlist_append",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ pr : \{w}, ∀ nx : \{w}, tlsf_small_dlist(pr,APPEND(a,z),nx) == star(tlsf_small_dlist(pr,a,tlsf_small_first(z,nx)),tlsf_small_dlist(tlsf_small_last(pr,a),z,nx))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([@lists.append(), nil, lastnil] + ac),
        gen,
        arw(
          [
            thm("tlsf_small_dlist_cons"),
            thm("tlsf_small_first_append"),
            thm("tlsf_small_last_cons"),
          ] +
          ac,
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_dlist_tail",
    "∀ xs : \{lw}, ∀ pr : \{w}, ∀ nx : \{w}, tlsf_small_dlist(pr,xs,nx) == star(tlsf_small_dtail(pr,xs),(if xs == NIL { emp } else { pts(val(tlsf_small_last(pr,xs))+28,serialise_i32(nx)) }))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([nil, thm("tlsf_small_dtail")] + ac),
        gen,
        arw([
          thm("tlsf_small_dlist_cons"),
          thm("tlsf_small_last_cons"),
          @lists.not_cons_nil(),
        ]),
        @class.cond_cases_tac,
        arw([thm("tlsf_small_dtail"), thm("tlsf_small_first"), lastnil] + ac),
      ])
    },
  )
}
