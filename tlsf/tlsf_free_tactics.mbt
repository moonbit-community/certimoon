// A local claim must close before continuing to the next allocator step.

///|
fn free_have(s : String, proof : @tactics.Tactic) -> @tactics.Tactic raise {
  have(s, g => {
    solve(proof)(g) catch {
      err => {
        ignore(show_goal("free claim: " + s)(g))
        raise err
      }
    }
  })
}

///|
fn free_intro() -> @tactics.Tactic {
  g => {
    let (p, _, _, _) = triple_l_terms(g.1)
    let p = @equal.rhs(@kernel.concl(norm_conv()(p)))
    if args_of(p, "st", 3) is Some(_) {
      @tactics.all_tac(g)
    } else {
      seq([@tactics.conv_tac(pre_conv(norm_conv())), intro_tac(), free_intro()])(
        g,
      )
    }
  }
}

///|
fn free_at(s : String, tac : @tactics.Tactic) -> @tactics.Tactic {
  g => {
    tac(g) catch {
      err => {
        ignore(show_goal(s)(g))
        raise err
      }
    }
  }
}

///|
fn free_apply(th : @kernel.Thm) -> @tactics.Tactic raise {
  let th = @simp.rewrite_rule(ths([@class.eta_ax()]))(@bool.spec_all(th))
  if @basics.is_imp(@kernel.concl(th)) {
    seq([
      @simp.rewrite_tac(ths([@class.eta_ax()])),
      @tactics.match_mp_tac(th),
      @simp.asm_rewrite_tac(ths([])),
    ])
  } else {
    seq([
      @simp.rewrite_tac(ths([@class.eta_ax()])),
      @tactics.match_accept_tac(th),
    ])
  }
}

///|
fn free_lift(th : @kernel.Thm) -> @tactics.Tactic raise {
  let th = @simp.rewrite_rule(ths([@class.eta_ax()]))(@bool.spec_all(th))
  let c = @kernel.concl(th)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  if args_of(body, "sl_triple_m", 7) is Some(_) {
    seq([@tactics.match_mp_tac(thm("sl_triple_g_of_m_closed")), free_apply(th)])
  } else {
    seq([
      @tactics.match_mp_tac(thm("sl_triple_g_of")),
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(call_free_tac()),
          solve(
            seq([@tactics.match_mp_tac(thm("sl_triple_l_of")), free_apply(th)]),
          ),
        ]),
      ),
    ])
  }
}

///|
fn free_g_conseq(
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
    _ => raise Failure("free_g_conseq: not an allocator triple")
  }
  g => {
    let (_, _, _, labels) = triple_l_terms(g.1)
    seq([
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(p),
      @tactics.exists_tac(q),
      @tactics.exists_tac(labels),
      @simp.rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(pre),
          solve(core),
          solve(post),
          solve(
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              beta_goal(),
              @tactics.disch_tac,
              @simp.asm_rewrite_tac(ths([])),
            ]),
          ),
        ]),
      ),
    ])(g)
  }
}
