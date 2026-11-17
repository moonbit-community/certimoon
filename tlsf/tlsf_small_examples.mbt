// Nonempty witnesses: a four-slot page with live, cached and local slots.
// These also guard against an inconsistent or accidentally vacuous model.

///|
fn prove_tlsf_small_examples() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let base_defs = [
    "tlsf_small_total", "tlsf_small_slots", "tlsf_small_slot", "tlsf_small_used",
    "tlsf_count",
  ].map(thm)
  let conv = @wasm.compute_conv(base_defs + [@lists.filter(), @lists.mem()], suc=[
    ("tlsf_small_slots", 3, 2),
  ])
  let p = "(word(2176) : \{w})"
  let loc = "[(word(2736) : \{w}),word(3000)]"
  let cached = "[(word(2472) : \{w})]"
  let live = "[(word(2208) : \{w})]"
  let _ = lemma(
    "tlsf_small_example_partition",
    "tlsf_small_partition(\{p},256,\{loc},\{cached},\{live})",
    () => {
      seq([
        rw([thm("tlsf_small_partition")]),
        @tactics.conv_tac(conv),
        gen,
        @tactics.repeat_tac(
          @tactics.then_tac(
            @class.cond_cases_tac,
            seq([
              subst_vars(),
              @tactics.rule_assum_tac(th => @equal.conv_rule(conv, th)),
              arw([]),
              @tactics.conv_tac(conv),
            ]),
          ),
        ),
        arw([]),
        @tactics.conv_tac(conv),
        small_meson(ths([])),
      ])
    },
  )
  let sz = "(p : \{w}) => (256 : Num)"
  let lo = "(p : \{w}) => \{loc}"
  let ca = "(p : \{w}) => \{cached}"
  let li = "(p : \{w}) => \{live}"
  let fast = "(j : Num) => if j == 32 { \{cached} } else { (NIL : \{lw}) }"
  let part = "(j : Num) => if j == 32 { [\{p}] } else { (NIL : \{lw}) }"
  let same = seq([
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    arw([]),
    @tactics.conv_tac(conv),
  ])
  let _ = lemma(
    "tlsf_small_example_lists",
    "tlsf_small_lists_ok([\{p}],\{sz},\{lo},\{ca},\{li},\{fast},\{part})",
    () => {
      seq([
        rw([thm("tlsf_small_lists_ok")]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(
              seq([
                gen,
                @tactics.conv_tac(conv),
                same,
                gen,
                @tactics.conv_tac(conv),
                same,
              ]),
            ),
            solve(
              seq([
                gen,
                @class.asm_cases_tac(tm("(j : Num) == 32")),
                arw([@lists.mem()]),
                @tactics.conv_tac(conv),
                same,
                @tactics.exists_tac(tm(p)),
                @tactics.conv_tac(conv),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_example_backing",
    "tlsf_small_backing([\{p}],(p : \{w}) => (word(1091) : \{w}),[\{p}],\{sz},\{lo},\{ca},\{li},65536)",
    () => {
      seq([
        rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
        gen,
        @tactics.conv_tac(
          @wasm.compute_conv(
            base_defs + [thm("tlsf_used"), thm("tlsf_size"), @lists.mem()],
            suc=[("tlsf_small_slots", 3, 2)],
          ),
        ),
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        @tactics.rule_assum_tac(th => @equal.conv_rule(conv, th)),
        arw([thm("tlsf_small_example_partition")]),
        @tactics.conv_tac(conv),
      ])
    },
  )
}
