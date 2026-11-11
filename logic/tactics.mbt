// Tactic helpers the proofs share: for goals, assumptions and terms.
//
// - subst_vars, subst_only, merge_by, split_conjs, use_eqs, rw_inst: work
//   on the assumptions (substituting, merging, splitting, rewriting);
// - have, solve, by_lemma, forward2, forward2_3: steps of a proof;
// - arith, step_cases_of, rule_with: theorems (arithmetic, what a
//   configuration steps to, a rule of an inductive relation);
// - args_of, head_name, eq_of, triple_l_terms, with_spec: reading and
//   making terms;
// - show_goal, beta_goal: debugging, and beta-reducing a goal.

///|
/// Substitutes the assumptions `x == t` (x a variable) everywhere.
pub fn subst_vars() -> @tactics.Tactic {
  @tactics.repeat_tac(@tactics.first_x_assum(@tactics.subst_var_tac))
}

///|
/// Substitutes the assumption `x == t` (or `t == x`), x the variable named
/// `name`, everywhere.
pub fn subst_only(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    let is_it = (t : @kernel.Term) => t is Var(n, _) && n == name
    if @basics.is_eq(c) && (is_it(@equal.lhs(c)) || is_it(@equal.rhs(c))) {
      @tactics.subst_var_tac(th)
    } else {
      @tactics.no_tac
    }
  })
}

///|
/// Rewrites the other assumptions with one whose left side is an
/// application of the constant `name` (and drops it): two equations for
/// the same thing become an equation between their right sides.
fn merge_by(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    if @basics.is_eq(c) && @basics.strip_comb(@equal.lhs(c)).0 is Const(n, _) && n == name {
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th])))
    } else {
      @tactics.no_tac
    }
  })
}

///|
/// Splits the assumptions that are conjunctions.
pub fn split_conjs() -> @tactics.Tactic {
  @tactics.repeat_tac(
    @tactics.first_x_assum(th => if @basics.is_conj(@kernel.concl(th)) {
      @tactics.strip_assume_tac(th)
    } else {
      @tactics.no_tac
    }),
  )
}

///|
/// Rewrites the goal and the assumptions with the assumptions that are
/// equations `pick` accepts.
pub fn use_eqs(pick : (@kernel.Term) -> Bool) -> @tactics.Tactic {
  g => {
    let eqs = g.0.to_array().filter(a => pick(@kernel.concl(a.1))).map(a => a.1)
    seq([@tactics.rule_assum_tac(@simp.rewrite_rule(ths(eqs))), @simp.rewrite_tac(ths(eqs))])(g)
  }
}

///|
/// Whether `t` is an equation whose left side starts with `f`.
pub fn eq_of(t : @kernel.Term, f : String) -> Bool {
  if args_of(t, "=", 2) is Some([l, _]) {
    show(l).has_prefix(f)
  } else {
    false
  }
}

///|
/// Rewrites the goal and the other assumptions with the assumption
/// `f_inst(x) == ...`, x the variable named `name`.
fn rw_inst(name : String) -> @tactics.Tactic {
  @tactics.first_x_assum(th => {
    let c = @kernel.concl(th)
    let lhs_ok = @basics.is_eq(c) &&
      @basics.strip_comb(@equal.lhs(c)) is (Const("f_inst", _), args) &&
      args.to_array() is [Var(n, _)] &&
      n == name
    if lhs_ok {
      seq([
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths([th]))),
        @simp.rewrite_tac(ths([th])),
        @tactics.assume_tac(th),
      ])
    } else {
      @tactics.no_tac
    }
  })
}

///|
/// `t` as a new assumption, proved by `proof`.
pub fn have(t : String, proof : @tactics.Tactic) -> @tactics.Tactic raise {
  @tactics.thenl(
    @tactics.subgoal_then(tm(t), th => @tactics.assume_tac(th)),
    @list.List([proof, @tactics.all_tac]),
  )
}

///|
/// `tac`, failing unless it proves the goal: for `@tactics.first`, which
/// otherwise takes the first alternative that merely does not fail.
pub fn solve(tac : @tactics.Tactic) -> @tactics.Tactic {
  @tactics.then_tac(tac, @tactics.no_tac)
}

///|
/// mp_tac of `th` (∀ xs. a → b) at `args`, a from the assumptions, and b
/// taken apart into assumptions: for verification conditions.
pub fn by_lemma(th : @kernel.Thm, args : Array[String]) -> @tactics.Tactic raise {
  seq([
    @tactics.mp_tac(@bool.ispecl(@list.List(args.map(tm)), th)),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.try_tac(@tactics.disch_then(th => @tactics.strip_assume_tac(th))),
  ])
}

///|
/// `mp_tac` of `lemma` (∀ xs. A && B → C) applied to the first two
/// assumptions that match A and B.
pub fn forward2(lemma : @kernel.Thm) -> @tactics.Tactic {
  g => {
    let asms = g.0.to_array()
    for a in asms {
      for b in asms {
        let th : @kernel.Thm? = Some(@drule.match_mp(lemma)(@bool.conj(a.1, b.1))) catch {
          _ => None
        }
        if th is Some(th) {
          return @tactics.mp_tac(th)(g)
        }
      }
    }
    raise Failure("forward2: no assumptions match")
  }
}

///|
/// mp_tac of `lemma` (∀ xs. A && B && C && D → E) at assumptions that
/// match its premises (the first, then the rest), as forward2 does for two.
fn forward2_3(lemma : @kernel.Thm) -> @tactics.Tactic {
  g => {
    let asms = g.0.to_array()
    let prems = @basics.conjuncts(@basics.dest_imp(@basics.strip_forall(@kernel.concl(lemma)).1).0).to_array()
    let n = prems.length()
    // the assumptions each premise matches on its own
    let matches = (p : @kernel.Term, a : @kernel.Thm) => (try Some(@drule.term_match(@list.List([]), p, @kernel.concl(a))) catch {
      _ => None
    }) is Some(_)
    let cands = prems.map(p => asms.filter(a => matches(p, a.1)).map(a => a.1))
    // try every choice of them for the premises, in order
    fn go(k : Int, chosen : Array[@kernel.Thm]) -> @kernel.Thm? {
      if k == n {
        let mut c = chosen[n - 1]
        for j = n - 2; j >= 0; j = j - 1 {
          c = @bool.conj(chosen[j], c) catch { _ => return None }
        }
        return try Some(@drule.match_mp(lemma)(c)) catch { _ => None }
      }
      for a in cands[k] {
        if go(k + 1, chosen + [a]) is Some(th) {
          return Some(th)
        }
      }
      None
    }
    match go(0, []) {
      Some(th) => @tactics.mp_tac(th)(g)
      None => raise Failure("forward2_3: no assumptions match")
    }
  }
}

///|
/// The linear arithmetic fact `t`.
pub fn arith(t : String) -> @kernel.Thm raise {
  @int.arith_rule(tm(t))
}

///|
/// step_cases(s, f, code) without computing (`@wasm.step_cases`), kept
/// for the next rule about the same code: it is the slow part of a rule.
let step_cases_seen : Map[String, @kernel.Thm] = Map([])

///|
fn step_cases_of(s : @kernel.Term, f : @kernel.Term, code : String) -> @kernel.Thm raise {
  let key = show(s) + "|" + show(f) + "|" + code
  match step_cases_seen.get(key) {
    Some(th) => th
    None => {
      let th = @wasm.step_cases(s, f, tm(code), compute=false)
      step_cases_seen[key] = th
      th
    }
  }
}

///|
/// The rule among `rules` (a conjunction) whose statement mentions all of
/// `parts`.
fn rule_with(rules : @kernel.Thm, parts : Array[String]) -> @kernel.Thm raise {
  for r in @bool.conjuncts_rule(rules) {
    let text = show(@kernel.concl(r))
    if parts.iter().all(p => text.contains(p)) {
      return r
    }
  }
  raise Failure("certimoon/logic: no rule with " + parts.join(", "))
}

///|
/// The arguments of `name` applied to `n` arguments, if `t` is that.
pub fn args_of(t : @kernel.Term, name : String, n : Int) -> Array[@kernel.Term]? {
  let (f, args) = @basics.strip_comb(t)
  match f {
    Const(c, _) if c == name && args.length() == n => Some(args.to_array())
    _ => None
  }
}

///|
/// The name of the constructor at the head of `t`.
fn head_name(t : @kernel.Term) -> String {
  match @basics.strip_comb(t).0 {
    Const(c, _) => c
    _ => ""
  }
}

///|
/// The parts (p, bs, q, ls) of the term `sl_triple_l(p, bs, q, ls)`, or
/// of `sl_triple_g(G, fs, inst, rp, p, bs, q, ls)`.
fn triple_l_terms(
  t : @kernel.Term,
) -> (@kernel.Term, @kernel.Term, @kernel.Term, @kernel.Term) raise {
  let (_, args) = @basics.strip_comb(t)
  match args.to_array() {
    [p, bs, q, ls] => (p, bs, q, ls)
    [_, _, _, _, p, bs, q, ls] => (p, bs, q, ls)
    _ => raise Failure("certimoon/logic: not a triple with labels: " + show(t))
  }
}

///|
/// The term `text` with its variable `name` (a spec's P or Q) replaced by
/// the term `t`.
fn with_spec(text : String, name : String, t : @kernel.Term) -> @kernel.Term raise {
  let body = tm(text)
  guard @kernel.frees(body).to_array().filter(v => v is Var(n, _) && n == name) is [v] else {
    raise Failure("with_spec: no " + name)
  }
  @kernel.vsubst(@list.List([(t, v)]), body)
}

///|
/// Prints the goal (when tracing), for debugging proofs.
pub fn show_goal(label : String) -> @tactics.Tactic {
  g => {
    if trace.val {
      println("goal at " + label + ":")
      for a in g.0 {
        println("  [" + a.0 + "] " + show(@kernel.concl(a.1)))
      }
      println("  ⊢ " + show(g.1))
    }
    @tactics.all_tac(g)
  }
}

///|
pub fn beta_goal() -> @tactics.Tactic {
  @tactics.conv_tac(@equal.try_conv(@equal.redepth_conv(@equal.beta_conv)))
}
