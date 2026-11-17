// Reassemble separately owned link and slot arrays, then concatenate their
// byte intervals without assuming a particular order of local-list nodes.

///|
fn prove_tlsf_block_free_arrays() -> Unit raise {
  let ft = "(Num) -> \{hprop}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_small_istar_pair",
    "∀ n : Num, ∀ ff : \{ft}, ∀ gg : \{ft}, star(tlsf_istar(ff,n),tlsf_istar(gg,n)) == tlsf_istar((i : Num) => star(ff(i),gg(i)),n)",
    () => seq([@nums.induct_tac, rw([thm("tlsf_istar")] + ac), gen, arw(ac)]),
  )
  let _ = lemma(
    "tlsf_small_istar_mono",
    "∀ n : Num, ∀ ff : \{ft}, ∀ gg : \{ft}, (∀ i : Num, i < n → (∀ h : \{heap}, ff(i,h) → gg(i,h))) → (∀ h : \{heap}, tlsf_istar(ff,n,h) → tlsf_istar(gg,n,h))",
    () => {
      @tactics.thenl(
        @nums.induct_tac,
        @list.List([
          rw([thm("tlsf_istar")]),
          seq([
            gen,
            strip,
            @tactics.x_gen_tac(tm("(h : " + heap + ")")),
            @tactics.disch_tac,
            rw([thm("tlsf_istar")]),
            @tactics.match_mp_tac(
              inst(thm("star_mono"), [
                "tlsf_istar((ff : " + ft + "),(n : Num))",
                "tlsf_istar((gg : " + ft + "),(n : Num))",
                "(ff : " + ft + ")((n : Num))",
                "(gg : " + ft + ")((n : Num))",
                "(h : " + heap + ")",
              ]),
            ),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.first(
              @list.List([
                solve(
                  seq([
                    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                    small_meson(
                      ths([
                        arith("∀ i : Num, ∀ n : Num, i < n → i < SUC(n)"),
                      ]),
                    ),
                  ]),
                ),
                solve(small_meson(ths([arith("∀ n : Num, n < SUC(n)")]))),
                solve(
                  seq([
                    @tactics.undisch_tac(
                      tm(
                        "tlsf_istar((ff : " +
                        ft +
                        "),SUC(n),(h : " +
                        heap +
                        "))",
                      ),
                    ),
                    rw([thm("tlsf_istar")]),
                  ]),
                ),
              ]),
            ),
          ]),
        ]),
      )
    },
  )
  let zero = lemma(
    "tlsf_small_bytes_zero",
    "∀ a : Num, tlsf_bytes(a,0) == emp",
    () => {
      rw([
        thm("tlsf_bytes"),
        @lists.length_eq_nil(),
        @theorems.unwind_thm2(),
        thm("tlsf_initialize_pts_nil"),
        @class.eta_ax(),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_bytes_array",
    "∀ n : Num, ∀ a : Num, ∀ stride : Num, tlsf_istar((i : Num) => tlsf_bytes(a+stride*i,stride),n) == tlsf_bytes(a,stride*n)",
    () => {
      @tactics.thenl(
        @nums.induct_tac,
        @list.List([
          rw([thm("tlsf_istar"), @arith.mult_clauses(), zero]),
          seq([
            gen,
            rw([thm("tlsf_istar")]),
            arw([]),
            rw([
              arith("∀ s : Num, ∀ n : Num, s*SUC(n) == s*n+s"),
              thm("tlsf_bytes_split"),
            ]),
          ]),
        ]),
      )
    },
  )
}
