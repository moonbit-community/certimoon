// A result-producing if/block can propagate the specified abort as well.

///|
fn prove_abort_typed_controls() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let at = "(Wstore,Wframe) -> Bool"
  let vars = "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, ∀ a : \{at}"
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  let block = "[Basic(Block(Tbv((v : Option[Valtype])),(bs : List[B_e])))]"
  let enter = "[Label(LENGTH(tbv_results((v : Option[Valtype]))),NIL,MAP(Basic,(bs : List[B_e])))]"
  let blockstep = @simp.rewrite_rule(
    ths([@lists.map(), @lists.append(), thm("tbv_results"), @lists.length()]),
  )(
    @bool.ispecl(
      @list.List(
        [
          "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(v : Option[Valtype])",
          "(bs : List[B_e])",
        ].map(tm),
      ),
      thm("block_step"),
    ),
  )
  abort_control_step(
    "safe_abort_typed_block",
    "\{vars}, ∀ v : Option[Valtype], ∀ bs : List[B_e], safe_abort(n,s,f,MAP(Basic,bs),q,a) → safe_abort(SUC(n),s,f,\{block},q,a)",
    block,
    enter,
    @tactics.accept_tac(blockstep),
    seq([@tactics.match_mp_tac(thm("safe_abort_label")), arw([])]),
  )
  let i = "Basic(EConstNum(ConstInt32((c : \{w32}))))"
  let ifcode = "[\{i},Basic(If(Tbv((v : Option[Valtype])),(bs1 : List[B_e]),(bs2 : List[B_e])))]"
  let choice = "if ((c : \{w32}) == word(0)) { [Basic(Block(Tbv((v : Option[Valtype])),(bs2 : List[B_e])))] } else { [Basic(Block(Tbv((v : Option[Valtype])),(bs1 : List[B_e])))] }"
  abort_control_step(
    "safe_abort_typed_if",
    "\{vars}, ∀ v : Option[Valtype], ∀ c : \{w32}, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], (!(c == word(0)) → safe_abort(n,s,f,[Basic(Block(Tbv((v : Option[Valtype])),bs1))],q,a)) && (c == word(0) → safe_abort(n,s,f,[Basic(Block(Tbv((v : Option[Valtype])),bs2))],q,a)) → safe_abort(SUC(n),s,f,\{ifcode},q,a)",
    ifcode,
    choice,
    seq([
      @class.asm_cases_tac(tm("(c : \{w32}) == word(0)")),
      arw([]),
      @tactics.match_mp_tac(thm("abort_reduce_simple")),
      @tactics.first(
        @list.List([
          solve(seq([@tactics.match_mp_tac(rs[25]), arw([])])),
          solve(seq([@tactics.match_mp_tac(rs[26]), arw([])])),
        ]),
      ),
    ]),
    @meson.asm_meson_tac(ths([])),
  )
}
