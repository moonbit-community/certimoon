// Local tactic plumbing for checked startup composition.

///|
fn startup_forward(lemma : @kernel.Thm) -> @tactics.Tactic {
  g => {
    let asms = g.0.to_array()
    let prems = @basics.conjuncts(
      @basics.dest_imp(@basics.strip_forall(@kernel.concl(lemma)).1).0,
    ).to_array()
    let n = prems.length()
    // the assumptions each premise matches on its own
    let matches = (p : @kernel.Term, a : @kernel.Thm) => {
      (Some(@drule.term_match(@list.List([]), p, @kernel.concl(a))) catch {
        _ => None
      })
      is Some(_)
    }
    let cands = prems.map(p => asms.filter(a => matches(p, a.1)).map(a => a.1))
    // try every choice of them for the premises, in order
    fn go(k : Int32, chosen : Array[@kernel.Thm]) -> @kernel.Thm? {
      if k == n {
        let mut c = chosen[n - 1]
        for j = n - 2; j >= 0; j = j - 1 {
          c = @bool.conj(chosen[j], c) catch { _ => return None }
        }
        return Some(@drule.match_mp(lemma)(c)) catch { _ => None }
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
fn startup_rule_with(
  rules : @kernel.Thm,
  parts : Array[String],
) -> @kernel.Thm raise {
  for r in @bool.conjuncts_rule(rules) {
    let text = show(@kernel.concl(r))
    if parts.iter().all(p => text.contains(p)) {
      return r
    }
  }
  raise Failure("certimoon/logic: no rule with " + parts.join(", "))
}

///|
fn startup_meson(ths : @list.List[@kernel.Thm]) -> @tactics.Tactic raise {
  @meson.gen_meson_tac(0L, 6L, 1L, ths)
}

///|
fn startup_rw_inst(name : String) -> @tactics.Tactic {
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
fn startup_lift_facts() -> Array[@kernel.Thm] {
  [thm("lift"), thm("star_ex"), thm("star_pure"), @class.eta_ax()]
}

///|
fn startup_vc(extra~ : Array[@kernel.Thm] = []) -> @tactics.Tactic raise {
  let rws = extra +
    [
      @class.eta_ax(),
      @lists.append(),
      @lists.map(),
      thm("st"),
      thm("wasm_bool_zero"),
      thm("tlsf_initialize_valid"),
      @words.word_ugt_v1(),
      @words.word_uge_v1(),
      @words.val_word(),
      @words.dimindex_32(),
      @equal.gsym(@words.val_eq_0()),
      @wasm.thm("wasm_bool"),
    ]
  solve(
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.repeat_tac(@tactics.strip_tac),
      beta_goal(),
      @tactics.rule_assum_tac(th => {
        @equal.conv_rule(
          @calc_num.num_reduce_conv,
          @equal.conv_rule(
            @words.word_reduce_conv,
            @simp.rewrite_rule(ths(rws))(th),
          ),
        )
      }),
      split_conjs(),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.asm_rewrite_tac(ths(rws)),
      @tactics.conv_tac(@words.word_reduce_conv),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_rewrite_tac(ths(rws)),
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(ent_tac(rws, [])),
          solve(startup_meson(ths([]))),
        ]),
      ),
    ]),
  )
}
