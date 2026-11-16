///|
fn initialize_m_conseq(
  path : @kernel.Thm,
  pre : @tactics.Tactic,
  post : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let path = @simp.rewrite_rule(ths([@class.eta_ax(), @lists.append()]))(
    @bool.spec_all(path),
  )
  let c = @kernel.concl(path)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let (p, q, raw) = match
    (args_of(body, "sl_triple", 3), args_of(body, "sl_triple_m", 7)) {
    (Some([p, _, q]), _) => (p, q, true)
    (_, Some(a)) => (a[3], a[5], false)
    _ => raise Failure("initialize_m_conseq: expected a compiled triple")
  }
  let apply = free_apply(path)
  let core = if raw {
    seq([
      @tactics.match_mp_tac(thm("sl_triple_m_of")),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          call_free_tac(),
          seq([@tactics.match_mp_tac(thm("sl_triple_l_of")), apply]),
        ]),
      ),
    ])
  } else {
    apply
  }
  seq([
    @tactics.match_mp_tac(thm("sl_conseq_m")),
    @tactics.exists_tac(p),
    @tactics.exists_tac(q),
    @simp.rewrite_tac(ths([@class.eta_ax(), @lists.append()])),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([solve(pre), solve(core), solve(post)])),
  ])
}

///|
fn initialize_abort_conseq(
  path : @kernel.Thm,
  pre : @tactics.Tactic,
  post : @tactics.Tactic,
  on_abort~ : @tactics.Tactic = same_tac(),
) -> @tactics.Tactic raise {
  let path = @simp.rewrite_rule(ths([@class.eta_ax(), @lists.append()]))(
    @bool.spec_all(path),
  )
  let c = @kernel.concl(path)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  g => {
    let target = args_of(g.1, "sl_abort_m", 7).unwrap()
    let (p, q, a, core) = match
      (
        args_of(body, "sl_abort_m", 7),
        args_of(body, "sl_triple_m", 7),
        args_of(body, "sl_triple", 3),
      ) {
      (Some(xs), _, _) => (xs[3], xs[5], xs[6], free_apply(path))
      (_, Some(xs), _) =>
        (
          xs[3],
          xs[5],
          target[6],
          seq([
            @tactics.match_mp_tac(thm("sl_abort_m_of")),
            initialize_m_conseq(path, same_tac(), same_tac()),
          ]),
        )
      (_, _, Some(xs)) =>
        (
          xs[0],
          xs[2],
          target[6],
          seq([
            @tactics.match_mp_tac(thm("sl_abort_m_of")),
            initialize_m_conseq(path, same_tac(), same_tac()),
          ]),
        )
      _ => raise Failure("initialize_abort_conseq: expected a compiled triple")
    }
    seq([
      @tactics.match_mp_tac(thm("sl_abort_conseq_m")),
      @tactics.exists_tac(p),
      @tactics.exists_tac(q),
      @tactics.exists_tac(a),
      @simp.rewrite_tac(ths([@class.eta_ax(), @lists.append()])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([solve(pre), solve(core), solve(post), solve(on_abort)]),
      ),
    ])(g)
  }
}
