// The canonical physical slot enumeration has no duplicate addresses.

///|
fn prove_tlsf_block_free_slot_counts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let _gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let nil = lemma(
    "tlsf_small_count_nil",
    "∀ b : \{w}, tlsf_count(b,(NIL : \{lw})) == 0",
    rw([thm("tlsf_count"), @lists.filter(), @lists.length()]),
  )
  let inj = (n : String) => {
    "∀ i : Num, ∀ j : Num, i < \{n} && j < \{n} && tlsf_small_slot((p : \{w}),(s : Num),i) == tlsf_small_slot(p,s,j) → i == j"
  }
  let count = (n : String) => {
    "∀ b : \{w}, tlsf_count(b,tlsf_small_slots((p : \{w}),(s : Num),\{n})) == (if MEM(b,tlsf_small_slots(p,s,\{n})) { 1 } else { 0 })"
  }
  let _ = lemma(
    "tlsf_small_slots_counts",
    "∀ n : Num, ∀ p : \{w}, ∀ s : Num, (\{inj("n")}) → (\{count("n")})",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        rw([
          thm("tlsf_small_slots"),
          thm("tlsf_count"),
          @lists.filter(),
          @lists.length(),
          @lists.mem(),
        ]),
        seq([
          @tactics.x_gen_tac(tm("(p : " + w + ")")),
          @tactics.x_gen_tac(tm("(s : Num)")),
          @tactics.disch_tac,
          free_have(
            "∀ i : Num, ∀ j : Num, i < (n : Num) && j < n && tlsf_small_slot((p : \{w}),(s : Num),i) == tlsf_small_slot(p,s,j) → i == j",
            small_meson(
              ths([arith("∀ i : Num, ∀ n : Num, i < n → i < SUC(n)")]),
            ),
          ),
          free_have(
            count("(n : Num)"),
            seq([
              @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
              arw([]),
            ]),
          ),
          free_have(
            "!MEM(tlsf_small_slot((p : \{w}),(s : Num),(n : Num)),tlsf_small_slots(p,s,n))",
            seq([
              rw([thm("tlsf_small_slots_member")]),
              @class.refute_then(th => @tactics.strip_assume_tac(th)),
              free_have(
                "(n : Num) < SUC(n) && (i : Num) < SUC(n)", @int.asm_arith_tac,
              ),
              free_have("(n : Num) == (i : Num)", small_meson(ths([]))),
              @int.asm_arith_tac,
            ]),
          ),
          @tactics.x_gen_tac(tm("(b : " + w + ")")),
          rw([
            thm("tlsf_small_slots"),
            thm("tlsf_small_count_append"),
            thm("tlsf_small_count_cons"),
            nil,
            @lists.mem_append(),
            @lists.mem(),
          ]),
          arw([]),
          @class.asm_cases_tac(
            tm(
              "(b : " +
              w +
              ") == tlsf_small_slot((p : " +
              w +
              "),(s : Num),(n : Num))",
            ),
          ),
          subst_vars(),
          arw([@theorems.eq_sym_eq()]),
          @tactics.repeat_tac(@class.cond_cases_tac),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ]),
    ),
  )
}
