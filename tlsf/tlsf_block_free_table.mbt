// The other 32 classes and every fast-list entry stay in the frame.

///|
fn prove_tlsf_block_free_table() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let v = "∀ d : \{w}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ k : Num"
  let rest = (p : String) => {
    "tlsf_istar((j : Num) => if j == (k : Num) { emp } else { tlsf_small_table_item((d : \{w}),(fast : (Num) -> \{lw}),\{p},j) },33)"
  }
  let part = "(partial : (Num) -> \{lw})"
  let _ = lemma(
    "tlsf_small_table_focus",
    "\{v}, k < 33 → tlsf_small_table(d,fast,partial) == star(tlsf_small_table_item(d,fast,partial,k),\{rest(part)})",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_small_table")]),
        @tactics.match_mp_tac(thm("tlsf_istar_focus")),
        arw([]),
      ])
    },
  )
  let new = "tlsf_small_put_class((partial : (Num) -> \{lw}),(k : Num),(entries : \{lw}))"
  let _ = lemma(
    "tlsf_small_table_update_rest",
    "\{v}, ∀ entries : \{lw}, \{rest(new)} == \{rest(part)}",
    () => {
      seq([
        gen,
        @tactics.match_mp_tac(thm("tlsf_istar_cong")),
        @tactics.x_gen_tac(tm("(j : Num)")),
        @tactics.disch_tac,
        @class.asm_cases_tac(tm("(j : Num) == (k : Num)")),
        arw([]),
        rw([thm("tlsf_small_table_item"), thm("tlsf_small_put_class")]),
        arw([]),
      ])
    },
  )
}
