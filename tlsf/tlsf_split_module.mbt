///|
fn prove_tlsf_split_module() -> Unit raise {
  let w = w32
  let sa = sassn
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let z = "V_num(ConstInt32((word(0) : \{w})))"
  let zs = "[\{z}, \{z}, \{z}]"
  let ins = "[T_num(T_i32)]"
  let ts = "[T_num(T_i32), T_num(T_i32), T_num(T_i32)]"
  let addr = "sfunc_ind((inst : Inst), (push : Num))"
  let g = "tlsf_proved_spec(\{addr}, tlsf_push_code((d : \{w})), \{zs}, 1, 1)"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf(\{ins}, \{ins}), \{ts}, tlsf_push_code((d : \{w})))"
  let free = lemma("tlsf_push_call_free", "∀ d : \{w}, call_free_b(tlsf_push_code(d))", seq([gen, call_free_tac()]))
  let holds = inst(thm("tlsf_proved_specs"), ["(fs : List[Cl])", "(tabs : List[(Tab_t, List[V_ref])])", "(inst : Inst)", addr, "tlsf_push_code((d : \{w}))", zs, ts, ins, ins])
  let holds = @equal.conv_rule(@calc_num.num_reduce_conv, @simp.rewrite_rule(ths([@lists.length()]))(holds))
  let _ = lemma("tlsf_split_in_module", "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ P : \{sa}, ∀ Q : \{sa}, \{native} && sl_triple_g(\{g}, fs, tabs, inst, \{falsep}, P, tlsf_split_code(d, push), Q, NIL) → sl_triple_m(fs, tabs, inst, P, tlsf_split_code(d, push), Q, NIL)", seq([
    gen, strip, @tactics.match_mp_tac(thm("sl_triple_m_of_g")), @tactics.exists_tac(tm(g)),
    @tactics.thenl(@tactics.conj_tac, @list.List([
      seq([
        @tactics.match_mp_tac(holds), arw([free, @wasm.thm("n_zeros"), @wasm.thm("bitzero"), @wasm.thm("bitzero_num"), @wasm.thm("those"), @wasm.thm("map_option"), @lists.map()]),
      ]),
      @tactics.first_assum(th => @tactics.accept_tac(th)),
    ])),
  ]))
}
