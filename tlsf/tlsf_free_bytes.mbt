// A removed block's header becomes payload of the merged block. Only
// allocator-owned or explicitly relinquished bytes are absorbed here.

///|
fn prove_tlsf_free_bytes() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let eight = lemma(
    "tlsf_bytes_two_words",
    "∀ a : Num, tlsf_bytes(a,8) == ((h : \{heap}) => ∃ x : \{w}, ∃ y : \{w}, star(\{cell("a","x")},\{cell("a+4","y")},h))",
    () => {
      seq([
        gen,
        rw(
          [
            @equal.conv_rule(
              @calc_num.num_reduce_conv,
              inst(thm("tlsf_bytes_split"), ["(a : Num)", "4", "4"]),
            ),
            thm("tlsf_bytes_word"),
          ] +
          lift_rws(),
        ),
      ])
    },
  )
  let a = "(a : Num)"
  let n = "(n : Num)"
  let b = "(b : Num)"
  let sum = arith("(n : Num)+8+(b : Num) == n+(8+b)")
  let p = "star(tlsf_bytes(\{a},\{n}),star(\{cell("a+n","x")},star(\{cell("a+n+4","y")},star(tlsf_bytes(a+n+8,\{b}),(R : \{hprop})))))"
  let q = "star(tlsf_bytes(\{a},\{n}+8+\{b}),(R : \{hprop}))"
  let _ = lemma(
    "tlsf_free_join_bytes",
    "∀ a : Num, ∀ n : Num, ∀ b : Num, ∀ x : \{w}, ∀ y : \{w}, ∀ R : \{hprop}, ∀ h : \{heap}, \{p}(h) → \{q}(h)",
    () => {
      ent_tac(
        [
          sum,
          inst(thm("tlsf_bytes_split"), [a, n, "8+(b : Num)"]),
          inst(thm("tlsf_bytes_split"), ["(a : Num)+(n : Num)", "8", b]),
          eight,
        ],
        ["(x : \{w})", "(y : \{w})"],
      )
    },
  )
}
