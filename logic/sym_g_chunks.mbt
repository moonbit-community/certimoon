// General triples can be composed as exact fragments too. Their environment,
// return assertion and label assertions must match the enclosing proof.

///|
fn g_chunk_step(
  sym : Sym,
  p : @kernel.Term,
  code : @kernel.Term,
  goal : @kernel.Term,
) -> @tactics.Tactic? raise {
  guard args_of(goal, "sl_triple_g", 9) is Some(ga) else { return None }
  guard @basics.is_list(code) else { return None }
  let instructions = @basics.dest_list(code).to_array()
  let key = (a : Array[@kernel.Term], pre : @kernel.Term, bs : @kernel.Term) => {
    let mut t = @pair.mk_pair((pre, bs))
    for i in [0, 1, 2, 3, 4, 8] {
      t = @pair.mk_pair((a[i], t))
    }
    t
  }
  for original in sym.chunks {
    let fresh = fresh_spec(original, @kernel.frees(goal))
    let c = @kernel.concl(fresh)
    let tr = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
    guard args_of(tr, "sl_triple_g", 9) is Some(a) else { continue }
    let defs = match program_def(a[6]) {
      Some(d) => [d]
      None => []
    }
    let th = @simp.pure_rewrite_rule(ths(defs + [@class.eta_ax()]))(fresh)
    let c = @kernel.concl(th)
    let tr = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
    guard args_of(tr, "sl_triple_g", 9) is Some(a) else { continue }
    guard @basics.is_list(a[6]) else { continue }
    let count = @basics.dest_list(a[6]).length()
    if count < 1 || count > instructions.length() {
      continue
    }
    let prefix = @lists.mk_list(
      @list.List(instructions[:count].to_owned()),
      @kernel.type_of(instructions[0]),
    )
    guard (Some(
        @drule.term_match(
          @list.List([]),
          key(a, a[5], a[6]),
          key(ga, p, prefix),
        ),
      ) catch {
        _ => None
      })
      is Some(matching) else {
      continue
    }
    let th = @drule.instantiate_rule(matching, th)
    let rest = @lists.mk_list(
      @list.List(instructions[count:].to_owned()),
      @kernel.type_of(instructions[0]),
    )
    let apply = (closed : @kernel.Thm) => {
      let a = args_of(@kernel.concl(closed), "sl_triple_g", 9).unwrap()
      let app = @basics.mk_icomb(@basics.mk_icomb(tm("APPEND"), prefix), rest)
      let eq = @simp.rewrite_conv(ths([@lists.append()]))(app)
      seq([
        @tactics.subst1_tac(@equal.gsym(eq)),
        @tactics.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(a[7]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([@tactics.accept_tac(closed), sym_tac(sym)]),
        ),
      ])
    }
    return Some(
      if @basics.is_imp(@kernel.concl(th)) {
        @tactics.subgoal_then(@basics.dest_imp(@kernel.concl(th)).0, hth => {
          apply(@bool.mp(th, hth))
        })
      } else {
        apply(th)
      },
    )
  }
  None
}
