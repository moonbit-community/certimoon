///|
fn malloc_abort_vc(a : Array[String]) -> @tactics.Tactic raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.repeat_tac(@tactics.strip_tac)
  let fp = "(fp : " + rty + ")"
  let old = a[1]
  let transport = @tactics.try_tac(
    @tactics.first_assum(th => {
      guard args_of(@kernel.concl(th), "tlsf_malloc_result", 8) is Some(r) else {
        return @tactics.no_tac
      }
      let candidate = inst(thm("tlsf_malloc_result_original_frame"), [
        show(r[0]),
        show(r[1]),
        old,
        fp,
        show(r[4]),
        show(r[5]),
        show(r[6]),
        show(r[7]),
        show(r[2]),
      ])
      return g => {
        let converted = block_under(candidate, g) catch {
          _ => return @tactics.no_tac(g)
        }
        @tactics.assume_tac(converted)(g)
      }
    }),
  )
  let state = (g : @tactics.Goal) => {
    guard args_of(g.1, "tlsf_malloc_state", 6) is Some(target) else {
      return @tactics.no_tac(g)
    }
    @tactics.first_assum(th => {
      let c = @kernel.concl(th)
      let body = if args_of(c, "star", 3) is Some([x, y, _]) {
        @basics.list_mk_icomb("star", @list.List([x, y]))
      } else {
        c
      }
      let factors = malloc_star_factors(body)
      let found = factors.filter(x => head_name(x) == "tlsf_allocator").get(0)
      guard found is Some(allocator) else { return @tactics.no_tac }
      let model = @basics.strip_comb(allocator).1.to_array()
      if model.length() != 15 {
        return @tactics.no_tac
      }
      let rule = inst(
        thm("tlsf_malloc_frame_state"),
        model.map(show) + target[1:].to_owned().map(show),
      )
      seq([
        free_apply(rule),
        @simp.asm_rewrite_tac(ths(malloc_ac() + [@arith.le_refl()])),
      ])
    })(g)
  }
  seq([
    gen,
    @simp.rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
    strip,
    beta_goal(),
    transport,
    @tactics.first(
      @list.List([
        solve(malloc_vc(extra=[thm("tlsf_full_malloc_post")])),
        solve(state),
      ]),
    ),
  ])
}
