///|
fn prove_tlsf_ensure_write_full() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let f = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim2 : Num) && (fp : \{rty})(gs,ms,h)"
  let args = [
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(m : \{w})",
    "(hdr : \{w})",
    "(e : \{w})",
    f,
  ]
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ hdr : \{w}, ∀ e : \{w}, ∀ fp : \{rty}, ∀ lim2 : Num"
  for part in ["free", "used"] {
    let before = @simp.rewrite_rule(ths([@lists.append()]))(
      inst(thm("tlsf_ensure_" + part + "_before_size_raw"), args),
    )
    let after = @simp.rewrite_rule(ths([@lists.append()]))(
      inst(
        thm("tlsf_ensure_" + part + "_after_size_raw"),
        args + ["(lim2 : Num)"],
      ),
    )
    let bt = args_of(@kernel.concl(before), "sl_triple", 3).unwrap()
    let at = args_of(@basics.dest_imp(@kernel.concl(after)).1, "sl_triple", 3).unwrap()
    let mid = args_of(bt[2], "st", 3).unwrap()
    let sz = @simp.rewrite_rule(ths([@lists.append()]))(
      @bool.ispecl(
        @list.List([mid[0], mid[1], tm("(lim2 : Num)"), mid[2]]),
        thm("st_memory_size_at"),
      ),
    )
    let stp = args_of(@basics.dest_imp(@kernel.concl(sz)).1, "sl_triple", 3).unwrap()
    let _ = lemma(
      "tlsf_ensure_" + part + "_write_raw",
      "\{vars}, MOD(lim2,65536) == 0 → sl_triple(\{show(bt[0])},tlsf_ensure_" +
      part +
      "_write((d : \{w}),(pop : Num),(push : Num)),\{show(at[2])})",
      () => {
        seq([
          gen,
          @tactics.disch_tac,
          rw([thm("tlsf_ensure_" + part + "_write_parts")]),
          @tactics.match_mp_tac(thm("sl_seq")),
          @tactics.exists_tac(bt[2]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @tactics.accept_tac(before),
              seq([
                @tactics.subst1_tac(
                  @equal.gsym(
                    @simp.rewrite_conv(ths([@lists.append()]))(
                      tm(
                        "APPEND([Memory_size],tlsf_ensure_" +
                        part +
                        "_after_size((d : \{w}),(pop : Num),(push : Num)))",
                      ),
                    ),
                  ),
                ),
                @tactics.match_mp_tac(thm("sl_seq")),
                @tactics.exists_tac(stp[2]),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([
                    seq([
                      @tactics.match_mp_tac(sz),
                      gen,
                      beta_goal(),
                      rw(lift_rws()),
                      strip,
                      arw([]),
                    ]),
                    seq([@tactics.match_mp_tac(after), arw([])]),
                  ]),
                ),
              ]),
            ]),
          ),
        ])
      },
    )
  }
}
