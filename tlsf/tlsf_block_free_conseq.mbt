///|
fn block_g_conseq(
  path : @kernel.Thm,
  pre : @tactics.Tactic,
  post : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let path = @simp.rewrite_rule(ths([@class.eta_ax()]))(@bool.spec_all(path))
  let c = @kernel.concl(path)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let (p, q, core) = match
    (
      args_of(body, "sl_triple", 3),
      args_of(body, "sl_triple_m", 7),
      args_of(body, "sl_triple_g", 9),
    ) {
    (Some([p, _, q]), _, _) => (p, q, free_lift(path))
    (_, Some(a), _) => (a[3], a[5], free_lift(path))
    (_, _, Some(a)) => (a[5], a[7], free_apply(path))
    _ => raise Failure("block_g_conseq: not a compiled triple")
  }
  g => {
    let (_, _, _, labels) = triple_l_terms(g.1)
    seq([
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(p),
      @tactics.exists_tac(q),
      @tactics.exists_tac(labels),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          free_at("block pre", pre),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              free_at("block core", core),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_at("block post", post),
                  seq([
                    @simp.rewrite_tac(ths([])),
                    @tactics.repeat_tac(@tactics.gen_tac),
                    beta_goal(),
                    @tactics.repeat_tac(@tactics.strip_tac),
                    @simp.asm_rewrite_tac(ths([])),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ])(g)
  }
}
