///|
fn prove_tlsf_free_phases() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let norm = [
    @equal.gsym(@lists.append_assoc()),
    @lists.append(),
    @lists.not_cons_nil(),
    @class.eta_ax(),
  ]
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ m0 : \{w}, ∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ fp : \{rty}"
  let native = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code((d : \{w})))"
  let params = "(d : \{w}),(lim : Num),(m0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fp : \{rty})"
  for prev in [true, false] {
    let dir = if prev { "prev" } else { "next" }
    let apply = (kind : String) => {
      seq([
        rw(norm),
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm))),
        @tactics.match_mp_tac(
          @simp.rewrite_rule(ths(norm))(
            @bool.spec_all(thm("tlsf_free_\{dir}_\{kind}_path")),
          ),
        ),
        arw(norm),
      ])
    }
    let remaining = if prev { "(zs : \{lw})" } else { "(t : \{lw})" }
    let free_case = seq([
      @tactics.strip_assume_tac(inst(@lists.list_cases(), [remaining])),
      subst_vars(),
      @tactics.first(
        @list.List([solve(apply("last")), solve(apply("interior"))]),
      ),
    ])
    let neighbour = if prev { "(e : \{w})" } else { "(h : \{w})" }
    let neighbour_case = seq([
      @class.asm_cases_tac(tm("tlsf_used((hd : \{ht})(\{neighbour}))")),
      @tactics.first(@list.List([solve(apply("used")), solve(free_case)])),
    ])
    let _ = lemma(
      "tlsf_free_\{dir}_phase",
      "\{vars}, \{native} → sl_triple_g(G,fs,tabs,inst,rp,tlsf_free_work(\{params}," +
      (if prev { "F,F" } else { "T,F" }) +
      "),tlsf_free_\{dir}(d,pop,push),tlsf_free_work(\{params}," +
      (if prev { "T,F" } else { "T,T" }) +
      "),labels)",
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.conv_tac(
          pre_conv(@simp.rewrite_conv(ths([thm("tlsf_free_work")]))),
        ),
        free_at("phase intro", free_intro()),
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm))),
        @tactics.strip_assume_tac(
          if prev {
            inst(thm("snoc_cases"), ["(ys : \{lw})"])
          } else {
            inst(@lists.list_cases(), ["(zs : \{lw})"])
          },
        ),
        subst_vars(),
        free_at(
          "phase cases",
          @tactics.first(
            @list.List([solve(apply("boundary")), solve(neighbour_case)]),
          ),
        ),
      ]),
    )
  }
}
