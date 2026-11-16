// The initializer's unit blocks and conditionals can propagate a specified
// abort. Their entry steps themselves leave both store and frame unchanged.

///|
fn abort_control_step(
  name : String,
  statement : String,
  code : String,
  enter : String,
  progress : @tactics.Tactic,
  finish : @tactics.Tactic,
) -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let cases = @wasm.step_cases(s, f, tm(code))
  ignore(
    lemma(
      name,
      statement,
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(thm("safe_abort_step")),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.exists_tac(s),
              @tactics.exists_tac(f),
              @tactics.exists_tac(tm(enter)),
              progress,
            ]),
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              @tactics.disch_then(th => {
                @tactics.mp_tac(@drule.match_mp(cases)(th))
              }),
              @simp.asm_rewrite_tac(
                ths([
                  thm("tb_tf_tbv"),
                  thm("tbv_results"),
                  @lists.length(),
                  @lists.map(),
                  @lists.append(),
                ]),
              ),
              @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
              @tactics.repeat_tac(@tactics.strip_tac),
              subst_vars(),
              finish,
            ]),
          ]),
        ),
      ]),
    ),
  )
}

///|
fn prove_abort_controls() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let at = "(Wstore,Wframe) -> Bool"
  let vars = "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ q : \{assn}, ∀ a : \{at}"
  let rs = @bool.conjuncts_rule(@wasm.thm("reduce_simple_rules")).to_array()
  abort_control_step(
    "safe_abort_unreachable_step",
    "\{vars}, a(s,f) → safe_abort(SUC(n),s,f,[Basic(Unreachable)],q,a)",
    "[Basic(Unreachable)]",
    "[Trap]",
    seq([
      @tactics.match_mp_tac(thm("abort_reduce_simple")),
      @tactics.match_accept_tac(rs[20]),
    ]),
    seq([@tactics.match_mp_tac(thm("safe_abort_trap")), arw([])]),
  )
  let _ = lemma(
    "safe_abort_unreachable",
    "\{vars}, a(s,f) → safe_abort(n,s,f,[Basic(Unreachable)],q,a)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @tactics.first(
        @list.List([
          solve(rw([thm("safe_abort")])),
          solve(
            seq([
              @tactics.match_mp_tac(thm("safe_abort_unreachable_step")),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let block = "[Basic(Block(Tbv(NONE),(bs : List[B_e])))]"
  let enter = "[Label(0,NIL,MAP(Basic,(bs : List[B_e])))]"
  let blockstep = @simp.rewrite_rule(
    ths([@lists.map(), @lists.append(), thm("tbv_results"), @lists.length()]),
  )(
    @bool.ispecl(
      @list.List(
        [
          "(s : Wstore)", "(f : Wframe)", "(NIL : List[Value])", "(NONE : Option[Valtype])",
          "(bs : List[B_e])",
        ].map(tm),
      ),
      thm("block_step"),
    ),
  )
  abort_control_step(
    "safe_abort_unit_block",
    "\{vars}, ∀ bs : List[B_e], safe_abort(n,s,f,MAP(Basic,bs),q,a) → safe_abort(SUC(n),s,f,\{block},q,a)",
    block,
    enter,
    @tactics.accept_tac(blockstep),
    seq([@tactics.match_mp_tac(thm("safe_abort_label")), arw([])]),
  )
  let i = "Basic(EConstNum(ConstInt32((c : \{w32}))))"
  let ifcode = "[\{i},Basic(If(Tbv(NONE),(bs1 : List[B_e]),(bs2 : List[B_e])))]"
  let choice = "if ((c : \{w32}) == word(0)) { [Basic(Block(Tbv(NONE),(bs2 : List[B_e])))] } else { [Basic(Block(Tbv(NONE),(bs1 : List[B_e])))] }"
  abort_control_step(
    "safe_abort_unit_if",
    "\{vars}, ∀ c : \{w32}, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], (!(c == word(0)) → safe_abort(n,s,f,[Basic(Block(Tbv(NONE),bs1))],q,a)) && (c == word(0) → safe_abort(n,s,f,[Basic(Block(Tbv(NONE),bs2))],q,a)) → safe_abort(SUC(n),s,f,\{ifcode},q,a)",
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
