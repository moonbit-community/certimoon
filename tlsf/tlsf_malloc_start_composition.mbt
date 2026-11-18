// Tactics instantiate checked composition rules; they add no logical axioms.

///|
fn startup_lift_g(path : @kernel.Thm) -> @tactics.Tactic raise {
  let path = @simp.rewrite_rule(ths([@class.eta_ax()]))(@bool.spec_all(path))
  let c = @kernel.concl(path)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let a = args_of(body, "sl_triple_g", 9).unwrap()
  seq([
    @tactics.match_mp_tac(thm("tlsf_sl_abort_r_of_g")),
    @tactics.exists_tac(a[0]),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        @tactics.match_accept_tac(thm("tlsf_start_empty_specs")),
        free_apply(path),
      ]),
    ),
  ])
}

///|
fn startup_lift_m(path : @kernel.Thm) -> @tactics.Tactic raise {
  seq([@tactics.match_mp_tac(thm("tlsf_sl_abort_r_of_m")), free_apply(path)])
}

///|
fn startup_conseq(
  path : @kernel.Thm,
  core : @tactics.Tactic,
  vc : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let c = @kernel.concl(@bool.spec_all(path))
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let a = args_of(body, "tlsf_sl_abort_r", 9).unwrap()
  seq([
    @tactics.match_mp_tac(thm("tlsf_sl_abort_r_conseq")),
    @tactics.exists_tac(a[4]),
    @tactics.exists_tac(a[6]),
    @tactics.exists_tac(a[8]),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([solve(core), solve(same_tac()), solve(vc)])),
  ])
}

///|
fn startup_weaken(
  path : @kernel.Thm,
  core : @tactics.Tactic,
  vc : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let c = @kernel.concl(@bool.spec_all(path))
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let a = args_of(body, "tlsf_sl_abort_r", 9).unwrap()
  g => {
    let b = args_of(g.1, "tlsf_sl_abort_r", 9).unwrap()
    let la = @basics.dest_list(a[7]).head().unwrap()
    let lb = @basics.dest_list(b[7]).head().unwrap()
    let rule = @bool.ispecl(
      @list.List(
        a[:3].to_owned() +
        [a[3], b[3], a[4], b[4], a[5], a[6], b[6], la, lb, a[8], b[8]],
      ),
      thm("tlsf_sl_abort_r_weaken"),
    )
    seq([
      @tactics.match_mp_tac(rule),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(@list.List([solve(core), solve(same_tac()), solve(vc)])),
    ])(g)
  }
}

///|
fn startup_intro_ex() -> @tactics.Tactic {
  g => {
    guard args_of(g.1, "tlsf_sl_abort_r", 9) is Some(a) else {
      return @tactics.no_tac(g)
    }
    let (vs, body) = @basics.strip_abs(a[4])
    let (x, inner) = @basics.dest_exists(body)
    let p = @basics.list_mk_abs(@list.List([x] + vs.to_array()), inner)
    let rule = @bool.ispecl(
      @list.List(a[:4].to_owned() + [p] + a[5:].to_owned()),
      thm("tlsf_sl_abort_r_ex"),
    )
    seq([
      beta_goal(),
      @tactics.match_mp_tac(@equal.beta_rule(rule)),
      @tactics.gen_tac,
    ])(g)
  }
}

///|
fn startup_r_of_g(path : @kernel.Thm, abort : String) -> @kernel.Thm raise {
  let path = @bool.spec_all(path)
  let c = @kernel.concl(path)
  let (need, body) = if @basics.is_imp(c) {
    @basics.dest_imp(c)
  } else {
    (tm("T"), c)
  }
  let a = args_of(body, "sl_triple_g", 9).unwrap()
  let rule = @bool.ispecl(
    @list.List(a[1:4].to_owned() + [a[0]] + a[4:].to_owned() + [tm(abort)]),
    thm("tlsf_sl_abort_r_of_g"),
  )
  let empty = @bool.ispecl(
    @list.List(a[1:4].to_owned()),
    thm("tlsf_start_empty_specs"),
  )
  let fact = if @basics.is_imp(c) { @bool.undisch(path) } else { path }
  @bool.disch(need, @bool.mp(rule, @bool.conj(empty, fact)))
}

///|
fn startup_r_of_m(
  path : @kernel.Thm,
  rp : String,
  labels : String,
) -> @kernel.Thm raise {
  let path = @bool.spec_all(path)
  let c = @kernel.concl(path)
  let (need, body) = if @basics.is_imp(c) {
    @basics.dest_imp(c)
  } else {
    (tm("T"), c)
  }
  let a = args_of(body, "sl_abort_m", 7).unwrap()
  let rule = @bool.ispecl(
    @list.List(
      a[:3].to_owned() + [tm(rp)] + a[3:6].to_owned() + [tm(labels), a[6]],
    ),
    thm("tlsf_sl_abort_r_of_m"),
  )
  let fact = if @basics.is_imp(c) { @bool.undisch(path) } else { path }
  @bool.disch(need, @bool.mp(rule, fact))
}
