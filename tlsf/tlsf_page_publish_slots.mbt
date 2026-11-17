// Publication transfers exactly one free payload to the new client. Other
// slots retain their ownership, including every old live payload omission.

///|
fn prove_tlsf_page_publish_slots() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let vs = "∀ n : Num, ∀ p : " +
    w +
    ", ∀ s : Num, ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", ∀ i : Num"
  let old = "tlsf_small_slot_heap((p : " +
    w +
    "),(s : Num),(live : " +
    lw +
    "))"
  let newer = "tlsf_small_slot_heap((p : " +
    w +
    "),(s : Num),CONS((b : " +
    w +
    "),(live : " +
    lw +
    ")))"
  let rest = "tlsf_istar((j : Num) => if j == (i : Num) { emp } else { " +
    old +
    "(j) },(n : Num))"
  let cond = "i < n && b == tlsf_small_slot(p,s,i) && !MEM(b,live) && (∀ j : Num, j < n && !(j == i) → !(tlsf_small_slot(p,s,j) == b))"
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_page_publish_slot_rest",
    vs +
    ", (∀ j : Num, j < n && !(j == i) → !(tlsf_small_slot(p,s,j) == b)) → tlsf_istar((j : Num) => if j == i { emp } else { " +
    newer +
    "(j) },n) == " +
    rest,
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("tlsf_istar_cong")),
      @tactics.x_gen_tac(tm("(j : Num)")),
      @tactics.disch_tac,
      @class.asm_cases_tac(tm("(j : Num) == (i : Num)")),
      arw([]),
      free_have(
        "!(tlsf_small_slot((p : " +
        w +
        "),(s : Num),(j : Num)) == (b : " +
        w +
        "))",
        small_meson(ths([])),
      ),
      rw([thm("tlsf_small_slot_heap"), @lists.mem()]),
      arw([]),
    ]),
  )
  let fields = [
    "pts(val((b : " + w + ")),serialise_i32((word(4) : " + w + ")))",
    "pts(val((b : " + w + "))+4,serialise_i32((p : " + w + ")))",
  ]
  for after in [false, true] {
    let target = if after { newer } else { old }
    let own = small_star(
      fields +
      (if after {
        []
      } else {
        ["tlsf_bytes(val((b : " + w + "))+12,(s : Num)-4)"]
      }) +
      [rest],
    )
    let _ = lemma(
      "tlsf_page_publish_slots_" + (if after { "post" } else { "pre" }),
      vs + ", " + cond + " → tlsf_istar(" + target + ",n) == " + own,
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          "!MEM(tlsf_small_slot((p : " +
          w +
          "),(s : Num),(i : Num)),(live : " +
          lw +
          "))",
          seq([
            @tactics.undisch_tac(
              tm("!MEM((b : " + w + "),(live : " + lw + "))"),
            ),
            arw([]),
          ]),
        ),
        g => {
          let focus = block_under(
            inst(thm("tlsf_istar_focus"), ["(n : Num)", target, "(i : Num)"]),
            g,
          )
          let focus = if after {
            @simp.rewrite_rule(
              ths([
                block_under(
                  inst(thm("tlsf_page_publish_slot_rest"), [
                    "(n : Num)",
                    "(p : " + w + ")",
                    "(s : Num)",
                    "(live : " + lw + ")",
                    "(b : " + w + ")",
                    "(i : Num)",
                  ]),
                  g,
                ),
              ]),
            )(focus)
          } else {
            focus
          }
          @tactics.subst1_tac(focus)(g)
        },
        rw([thm("tlsf_small_slot_heap"), @lists.mem()]),
        arw(ac),
      ]),
    )
  }
}
