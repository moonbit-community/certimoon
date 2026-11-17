///|
fn prove_tlsf_ensure_views() -> Unit raise {
  let b = "Word[8]"
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let zero = "pts((a : Num)+(n : Num),REPLICATE((k : Num),(word(0) : \{b})))"
  let old = "star(tlsf_bytes((a : Num),(n : Num)),\{zero})"
  let fresh = "tlsf_bytes((a : Num),(n : Num)+(k : Num))"
  let _ = lemma(
    "tlsf_grown_bytes_frame",
    "∀ a : Num, ∀ n : Num, ∀ k : Num, ∀ frame0 : \{hprop}, ∀ h : \{heap}, star(tlsf_bytes(a,n),star(\{zero},frame0),h) → star(\{fresh},frame0,h)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.match_mp_tac(
          inst(thm("star_mono"), [
            old,
            fresh,
            "(frame0 : \{hprop})",
            "(frame0 : \{hprop})",
            "(h : \{heap})",
          ]),
        ),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              @tactics.accept_tac(
                inst(thm("tlsf_grown_bytes"), [
                  "(a : Num)", "(n : Num)", "(k : Num)",
                ]),
              ),
            ),
            solve(seq([gen, @tactics.disch_tac, arw([])])),
            solve(
              seq([
                @tactics.undisch_tac(
                  tm(
                    "star(tlsf_bytes((a : Num),(n : Num)),star(\{zero},(frame0 : \{hprop})),(h : \{heap}))",
                  ),
                ),
                rw([thm("star_assoc")]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let n = "(n : Num)"
  let z = "(word(0) : \{w})"
  let cell = (a : String) => "pts(\{a},serialise_i32(\{z}))"
  let head = "star(\{cell("(a : Num)")},star(\{cell("a+4")},tlsf_bytes(a+8,n-8)))"
  let _ = lemma(
    "tlsf_new_memory_view",
    "∀ a : Num, ∀ n : Num, ∀ h : \{heap}, 8 <= n && pts(a,REPLICATE(n,(word(0) : \{b})),h) → \{head}(h)",
    () => {
      seq([
        gen,
        strip,
        have("4 <= \{n} && 4 <= n-4", @int.asm_arith_tac),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        @tactics.undisch_tac(
          tm("pts((a : Num),REPLICATE(\{n},(word(0) : \{b})),(h : \{heap}))"),
        ),
        @simp.asm_simp_tac(
          ths([
            inst(thm("tlsf_zeros_word"), ["(a : Num)", n]),
            inst(thm("tlsf_zeros_word"), ["(a : Num)+4", n + "-4"]),
            arith("(n : Num)-4-4 == n-8"),
            arith("(a : Num)+4+4 == a+8"),
          ]),
        ),
        ent_tac([thm("tlsf_bytes"), @lists.length_replicate()], [
          "REPLICATE((n : Num)-8,(word(0) : \{b}))",
        ]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_new_memory_frame",
    "∀ a : Num, ∀ n : Num, ∀ frame0 : \{hprop}, ∀ h : \{heap}, 8 <= n && star(pts(a,REPLICATE(n,(word(0) : \{b}))),frame0,h) → star(\{head},frame0,h)",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(
          inst(thm("star_mono"), [
            "pts((a : Num),REPLICATE((n : Num),(word(0) : \{b})))",
            head,
            "(frame0 : \{hprop})",
            "(frame0 : \{hprop})",
            "(h : \{heap})",
          ]),
        ),
        arw([]),
        gen,
        @tactics.disch_tac,
        @tactics.match_mp_tac(
          inst(thm("tlsf_new_memory_view"), [
            "(a : Num)",
            "(n : Num)",
            "(h1 : \{heap})",
          ]),
        ),
        arw([]),
      ])
    },
  )
}
