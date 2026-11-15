///|
fn prove_tlsf_split_payload() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let sum = arith("(a : Num) + 4 + 4 == a + 8 && a + 4 + 4 + 4 == a + 12")
  let s4 = (a : String, k : String) => @equal.conv_rule(@calc_num.num_reduce_conv, inst(thm("tlsf_bytes_split"), [a, "4", k]))
  let cell = (a : String, v : String) => "pts(\{a}, serialise_i32((\{v} : \{w})))"
  let words = "(h : \{heap}) => ∃ w0 : \{w}, ∃ w1 : \{w}, ∃ pf : \{w}, ∃ nf : \{w}, star(\{cell("(a : Num)", "w0")}, star(\{cell("a + 4", "w1")}, star(\{cell("a + 8", "pf")}, \{cell("a + 12", "nf")})), h)"
  let _ = lemma("tlsf_bytes_four_words", "∀ a : Num, tlsf_bytes(a, 16) == (\{words})", seq([
    gen, rw([s4("(a : Num)", "12"), s4("(a : Num) + 4", "8"), s4("(a : Num) + 4 + 4", "4"), sum, thm("tlsf_bytes_word")] + lift_rws()),
  ]))
  let lhs = "tlsf_bytes((a : Num), (z : Num))"
  let rhs = "star(tlsf_bytes((a : Num), (n : Num)), star(tlsf_bytes(a + n, 16), tlsf_bytes(a + n + 16, (s : Num) - 8)))"
  let _ = lemma("tlsf_split_payload_cut", "∀ a : Num, ∀ n : Num, ∀ s : Num, ∀ z : Num, 16 <= s && n + 8 + s == z → \{lhs} == \{rhs}", seq([
    gen, strip,
    have("(z : Num) == (n : Num) + (16 + ((s : Num) - 8))", @int.asm_arith_tac),
    @tactics.first_x_assum(th => if @basics.aconv(@equal.lhs(@kernel.concl(th)), tm("(z : Num)")) { @tactics.subst1_tac(th) } else { @tactics.no_tac }),
    rw([inst(thm("tlsf_bytes_split"), ["(a : Num)", "(n : Num)", "16 + ((s : Num) - 8)"]), inst(thm("tlsf_bytes_split"), ["(a : Num) + (n : Num)", "16", "(s : Num) - 8"])]),
  ]))
}
