// Symbolic composition for straight-line code and typed conditionals with
// an explicit abort postcondition. Branching blocks are supplied as checked
// closed fragments, so this tactic never assumes a rule for return or br.

///|
fn abort_arg_conv(i : Int32, c : @equal.Conv) -> @equal.Conv {
  let mut out = @equal.rand_conv(c)
  for _ in 0..<(6 - i) {
    out = @equal.rator_conv(out)
  }
  out
}

///|
fn abort_pre_conv(c : @equal.Conv) -> @equal.Conv {
  abort_arg_conv(3, c)
}

///|
fn abort_rule(goal : @kernel.Term, name : String) -> @kernel.Thm raise {
  let a = args_of(goal, "sl_abort_m", 7).unwrap()
  @bool.ispecl(@list.List(a[:3].to_owned()), thm(name))
}

///|
fn abort_closed_step(
  path : @kernel.Thm,
  rest : @kernel.Term,
  chunks : Array[@kernel.Thm],
  vc : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let t = @kernel.concl(path)
  let (p, code, q, core) = if args_of(t, "sl_abort_m", 7) is Some(a) {
    (a[3], a[4], a[5], @tactics.accept_tac(path))
  } else if args_of(t, "sl_triple_m", 7) is Some(a) {
    (
      a[3],
      a[4],
      a[5],
      seq([
        @tactics.match_mp_tac(thm("sl_abort_m_of")),
        @tactics.accept_tac(path),
      ]),
    )
  } else {
    let a = args_of(t, "sl_triple", 3).unwrap()
    (
      a[0],
      a[1],
      a[2],
      seq([
        @tactics.match_mp_tac(thm("sl_abort_m_of")),
        @tactics.match_mp_tac(thm("sl_triple_m_of")),
        @tactics.conj_tac,
        @tactics.first(
          @list.List([
            solve(call_free_tac()),
            solve(
              seq([
                @tactics.match_mp_tac(thm("sl_triple_l_of")),
                @tactics.accept_tac(path),
              ]),
            ),
          ]),
        ),
      ]),
    )
  }
  let app = @basics.list_mk_icomb("APPEND", @list.List([code, rest]))
  let eq = @simp.rewrite_conv(ths([@lists.append()]))(app)
  seq([
    @tactics.subst1_tac(@equal.gsym(eq)),
    @tactics.match_mp_tac(thm("sl_abort_seq_m")),
    @tactics.exists_tac(q),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([core, abort_sym_tac(chunks, vc)]),
    ),
  ])
}

///|
fn abort_chunk(
  chunks : Array[@kernel.Thm],
  vc : @tactics.Tactic,
  g : @tactics.Goal,
) -> @tactics.Tactic? raise {
  let ga = args_of(g.1, "sl_abort_m", 7).unwrap()
  guard @basics.is_list(ga[4]) else { return None }
  let code = @basics.dest_list(ga[4]).to_array()
  for original in chunks {
    let fresh = fresh_spec(original, @kernel.frees(g.1))
    let c = @kernel.concl(fresh)
    let tr = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
    let (i, j) = if args_of(tr, "sl_triple", 3) is Some(_) {
      (0, 1)
    } else if args_of(tr, "sl_triple_m", 7) is Some(_) ||
      args_of(tr, "sl_abort_m", 7) is Some(_) {
      (3, 4)
    } else {
      continue
    }
    let a = @basics.strip_comb(tr).1.to_array()
    let defs = match program_def(a[j]) {
      Some(d) => [d]
      None => []
    }
    let fresh = @simp.pure_rewrite_rule(ths(defs + [@class.eta_ax()]))(fresh)
    let c = @kernel.concl(fresh)
    let tr = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
    let a = @basics.strip_comb(tr).1.to_array()
    guard @basics.is_list(a[j]) else { continue }
    let n = @basics.dest_list(a[j]).length()
    if n < 1 || n > code.length() {
      continue
    }
    let prefix = @lists.mk_list(
      @list.List(code[:n].to_owned()),
      @kernel.type_of(code[0]),
    )
    let mut key = @pair.mk_pair((a[i], a[j]))
    let mut wanted = @pair.mk_pair((ga[3], prefix))
    if i == 3 {
      for k in [0, 1, 2] {
        key = @pair.mk_pair((a[k], key))
        wanted = @pair.mk_pair((ga[k], wanted))
      }
      if head_name(tr) == "sl_abort_m" {
        key = @pair.mk_pair((a[6], key))
        wanted = @pair.mk_pair((ga[6], wanted))
      }
    }
    guard (Some(@drule.term_match(@list.List([]), key, wanted)) catch {
        _ => None
      })
      is Some(matching) else {
      continue
    }
    let path = @drule.instantiate_rule(matching, fresh)
    let rest = @lists.mk_list(
      @list.List(code[n:].to_owned()),
      @kernel.type_of(code[0]),
    )
    let c = @kernel.concl(path)
    return Some(
      if @basics.is_imp(c) {
        seq([
          @tactics.subgoal_then(@basics.dest_imp(c).0, h => {
            abort_closed_step(@bool.mp(path, h), rest, chunks, vc)
          }),
          vc,
        ])
      } else {
        abort_closed_step(path, rest, chunks, vc)
      },
    )
  }
  None
}

///|
pub fn abort_sym_tac(
  chunks : Array[@kernel.Thm],
  vc : @tactics.Tactic,
) -> @tactics.Tactic {
  g => {
    let eta = @simp.pure_rewrite_conv(ths([@class.eta_ax()]))
    let normalized = @equal.rhs(@kernel.concl(eta(g.1)))
    if normalized != g.1 {
      return seq([@tactics.conv_tac(eta), abort_sym_tac(chunks, vc)])(g)
    }
    if (Some(solve(contra_tac())(g)) catch { _ => None }) is Some(done) {
      return done
    }
    let a = args_of(g.1, "sl_abort_m", 7).unwrap()
    if program_def(a[4]) is Some(d) {
      return seq([
        @tactics.conv_tac(abort_arg_conv(4, @simp.pure_rewrite_conv(ths([d])))),
        abort_sym_tac(chunks, vc),
      ])(g)
    }
    let p = @equal.rhs(@kernel.concl(norm_conv()(a[3])))
    let renorm = @tactics.conv_tac(abort_pre_conv(norm_conv()))
    if @basics.aconv(@basics.strip_abs(p).1, tm("F")) {
      return seq([renorm, @tactics.match_accept_tac(thm("sl_abort_false_m"))])(
        g,
      )
    }
    guard args_of(p, "st", 3) is Some(stargs) else {
      return seq([renorm, abort_intro_tac(), abort_sym_tac(chunks, vc)])(g)
    }
    if p != a[3] {
      return seq([renorm, abort_sym_tac(chunks, vc)])(g)
    }
    if abort_chunk(chunks, vc, g) is Some(tac) {
      return tac(g)
    }
    let code = @basics.dest_list(a[4]).to_array()
    if code.is_empty() {
      return seq([
        @tactics.match_mp_tac(thm("sl_abort_conseq_m")),
        @tactics.exists_tac(p),
        @tactics.exists_tac(p),
        @tactics.exists_tac(a[6]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(@tactics.match_accept_tac(thm("sl_abort_nil_m"))),
            solve(vc),
          ]),
        ),
      ])(g)
    }
    let instr = code[0]
    if head_name(instr) == "If" {
      if code.length() != 1 {
        raise Failure(
          "abort_sym_tac: provide a fragment for an if with a continuation from " +
          show(p) +
          "; next " +
          show(a[4]),
        )
      }
      return seq([
        @tactics.match_mp_tac(thm("sl_abort_typed_if_st_m")),
        @tactics.conj_tac,
        fact_tac(),
        abort_sym_tac(chunks, vc),
      ])(g)
    }
    if head_name(instr) == "Block" {
      if code.length() != 1 {
        raise Failure(
          "abort_sym_tac: provide a fragment for a block with a continuation",
        )
      }
      return seq([
        @tactics.match_mp_tac(thm("sl_abort_typed_block_st_m")),
        abort_sym_tac(chunks, vc),
      ])(g)
    }
    if head_name(instr) == "Unreachable" && code.length() == 1 {
      return seq([@tactics.match_mp_tac(thm("sl_abort_unreachable_m")), vc])(g)
    }
    let step = step_rule(step_rules, instr, p)
    let rest = @lists.mk_list(
      @list.List(code[1:].to_owned()),
      @kernel.type_of(instr),
    )
    if @basics.is_imp(@kernel.concl(step)) {
      seq([
        @tactics.subgoal_then(@basics.dest_imp(@kernel.concl(step)).0, h => {
          abort_closed_step(@bool.mp(step, h), rest, chunks, vc)
        }),
        vc,
      ])(g)
    } else {
      abort_closed_step(step, rest, chunks, vc)(g)
    }
  }
}
