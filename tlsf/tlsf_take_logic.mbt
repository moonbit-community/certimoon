///|
fn prove_tlsf_take_logic() -> Unit raise {
  let st = "(Num, (List[Value], List[Value], Num, \{heap}) -> Bool, (List[Value], List[Value], Num, \{heap}) -> Bool) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "sl_triple_g_of_m_closed",
    "∀ G : \{st}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ P : \{sassn}, ∀ code : List[B_e], ∀ Q : \{sassn}, ∀ labels : List[\{sassn}], sl_triple_m(fs, tabs, inst, P, code, Q, NIL) → sl_triple_g(G, fs, tabs, inst, rp, P, code, Q, labels)",
    () => {
      seq([
        gen,
        rw([
          thm("sl_triple_m"),
          thm("sl_triple_g"),
          thm("triple_l"),
          @lists.map(),
        ]),
        @tactics.disch_tac,
        gen,
        strip,
        @tactics.match_mp_tac(thm("safel_safer")),
        @tactics.match_mp_tac(thm("safe_safel")),
        @tactics.match_mp_tac(thm("safel_nil")),
        @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
        arw([@equal.gsym(@lists.el())]),
        // No escaping branch or return remains.
      ])
    },
  )
  let lc = "(lc : List[Value])"
  let fields = Array::makei(6, k => "EL(\{k}, \{lc})").join(", ")
  let _ = lemma(
    "tlsf_locals_six",
    "∀ lc : List[Value], LENGTH(lc) == 6 → lc == [\{fields}]",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(@lists.length_eq_list_of_seq(), ["(lc : List[Value])", "6"]),
        ),
        arw([]),
        @tactics.conv_tac(@equal.top_depth_conv(@lists.list_of_seq_conv)),
        beta_goal(),
        rw([@lists.el(), @lists.hd(), @lists.tl()]),
      ])
    },
  )
}
