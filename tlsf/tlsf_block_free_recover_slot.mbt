// A wholly allocator-owned slot can be forgotten back to its backing bytes.
// The client frame is retained verbatim rather than absorbed into the page.

///|
fn prove_tlsf_block_free_recover_slot() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let b = "tlsf_small_slot((p : \{w}),(s : Num),(i : Num))"
  let old = "star(tlsf_small_slot_heap((p : \{w}),(s : Num),(NIL : \{lw}),(i : Num)),star(tlsf_bytes(val(\{b})+8,4),(R : \{hprop})))"
  let new = "star(tlsf_bytes(val(\{b}),8+(s : Num)),(R : \{hprop}))"
  let _ = lemma(
    "tlsf_small_recover_slot",
    "∀ p : \{w}, ∀ s : Num, ∀ i : Num, ∀ R : \{hprop}, 8 <= s → (∀ h : \{heap}, \{old}(h) → \{new}(h))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have("12 <= 8+(s : Num)", @int.asm_arith_tac),
        g => {
          ent_tac(
            [
              block_under(
                inst(thm("tlsf_page_allocate_words3"), [
                  "val(" + b + ")",
                  "8+(s : Num)",
                ]),
                g,
              ),
              thm("tlsf_small_slot_heap"),
              @lists.mem(),
              thm("tlsf_bytes_word"),
              @arith.add_clauses(),
              arith("∀ s : Num, 8+s-12 == s-4"),
              arith("∀ a : Num, a+8+4 == a+12"),
            ],
            ["(word(4) : " + w + ")", "(p : " + w + ")", "(v : " + w + ")"],
          )(g)
        },
      ])
    },
  )
}
