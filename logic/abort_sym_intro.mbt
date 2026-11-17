// Exact-state introduction for triples with a specified trapping outcome.

///|
fn abort_intro_tac() -> @tactics.Tactic {
  g => {
    let a = args_of(g.1, "sl_abort_m", 7).unwrap()
    let (p, bs, q, ls) = (a[3], a[4], a[5], a[6])
    let (bvs, body) = @basics.strip_abs(p)
    guard bvs.to_array() is [vs, lc, gs, ms, h] else {
      raise Failure(
        "certimoon/logic: sym: the precondition is not an assertion: " + show(p),
      )
    }
    fn has_disjunction(t : @kernel.Term) -> Bool raise {
      if @basics.is_disj(t) {
        return true
      }
      if @basics.is_conj(t) {
        let (a, b) = @basics.dest_conj(t)
        return has_disjunction(a) || has_disjunction(b)
      }
      false
    }
    if has_disjunction(body) {
      return seq([
        @tactics.conv_tac(
          abort_pre_conv(
            @simp.pure_rewrite_conv(
              ths([@theorems.left_or_distrib(), @theorems.right_or_distrib()]),
            ),
          ),
        ),
        @tactics.match_mp_tac(abort_rule(g.1, "sl_abort_or_m")),
        @tactics.conj_tac,
      ])(g)
    }
    if @basics.is_exists(body) {
      let (x, b) = @basics.dest_exists(body)
      let pp = @basics.list_mk_abs(bvs.prepend(x), b)
      let th = @equal.beta_rule(
        @bool.ispecl(
          @list.List([pp, bs, q, ls]),
          abort_rule(g.1, "sl_abort_ex_m"),
        ),
      )
      return seq([@tactics.match_mp_tac(th), @tactics.gen_tac])(g)
    }
    if has_exists(body) {
      let rw = @simp.pure_rewrite_conv(
        ths([@theorems.left_and_exists_thm(), @theorems.right_and_exists_thm()]),
      )
      return @tactics.conv_tac(abort_pre_conv(rw))(g)
    }
    let mentions = (t : @kernel.Term, v : @kernel.Term) => @basics.free_in(v, t)
    let pure = (t : @kernel.Term) => {
      ![vs, lc, gs, ms, h].iter().any(v => mentions(t, v))
    }
    // facts && st(v, l, R)(vs, lc, gs, ms, h): the facts become assumptions
    if @basics.is_conj(body) {
      let (c, rest) = @basics.dest_conj(body)
      if pure(c) &&
        args_of(rest, "st", 8) is Some(args) &&
        args[3:].to_owned() == bvs.to_array() {
        let facts = subst_facts_tac()
        return seq([
          @tactics.match_mp_tac(abort_rule(g.1, "sl_abort_pure_m")),
          facts,
        ])(g)
      }
    }
    let conjs = @basics.conjuncts(body).to_array()
    let mut stack : @kernel.Term? = None
    let mut locals : @kernel.Term? = None
    let facts = []
    let rest = []
    for c in conjs {
      if args_of(c, "=", 2) is Some([a, b]) && a == vs && !mentions(b, vs) {
        stack = Some(b)
      } else if args_of(c, "=", 2) is Some([a, b]) &&
        a == lc &&
        !mentions(b, lc) {
        locals = Some(b)
      }
    }
    for c in conjs {
      if args_of(c, "=", 2) is Some([a, b]) && a == vs && !mentions(b, vs) {
        stack = Some(b)
      } else if args_of(c, "=", 2) is Some([a, b]) &&
        a == lc &&
        !mentions(b, lc) {
        locals = Some(b)
      } else if pure(c) {
        facts.push(c)
      } else if !mentions(c, vs) && !mentions(c, lc) {
        rest.push(c)
      } else {
        let subs = []
        if stack is Some(s) {
          subs.push((s, vs))
        }
        if locals is Some(l) {
          subs.push((l, lc))
        }
        let resolved = @kernel.vsubst(@list.List(subs), c)
        if !mentions(resolved, vs) && !mentions(resolved, lc) {
          rest.push(resolved)
        } else {
          raise Failure(
            "certimoon/logic: sym: cannot fix state arguments in " + show(c),
          )
        }
      }
    }
    guard stack is Some(s) && locals is Some(l) else {
      raise Failure(
        "certimoon/logic: sym: the precondition does not fix the stack and locals: " +
        show(p),
      )
    }
    let rbody = if rest.is_empty() {
      tm("T")
    } else {
      @bool.list_mk_conj(@list.List(rest))
    }
    let r = @basics.list_mk_abs(@list.List([gs, ms, h]), rbody)
    let r = @equal.rhs(@kernel.concl(norm_conv()(r)))
    let state = @basics.list_mk_comb(tm("st"), @list.List([s, l, r]))
    let p2 = if facts.is_empty() {
      state
    } else {
      let applied = @basics.list_mk_comb(state, bvs)
      @basics.list_mk_abs(
        bvs,
        @bool.mk_conj(@bool.list_mk_conj(@list.List(facts)), applied),
      )
    }
    @tactics.thenl(
      seq([
        @tactics.match_mp_tac(abort_rule(g.1, "sl_abort_pre_m")),
        @tactics.exists_tac(p2),
        @tactics.conj_tac,
      ]),
      @list.List([
        // the same conjuncts, rearranged
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @simp.rewrite_tac(ths([thm("st")])),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          subst_vars(),
          @simp.asm_rewrite_tac(ths([])),
          // the state's R is written out: so are the facts it came from
          @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm_thms()))),
          @simp.asm_rewrite_tac(ths([])),
          g => {
            raise Failure(
              "certimoon/logic: sym: cannot rearrange the precondition: " +
              show(g.1),
            )
          },
        ]),
        @tactics.all_tac,
      ]),
    )(g)
  }
}
