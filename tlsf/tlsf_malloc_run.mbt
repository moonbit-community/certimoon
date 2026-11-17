// Closed reachability corollaries: no helper triple or open specification
// occurs among the hypotheses of either execution theorem.

///|
fn prove_tlsf_malloc_runs() -> Unit raise {
  let model = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let runvars = [
    ("fr", hprop),
    ("s", "Wstore"),
    ("f", "Wframe"),
    ("vs", "List[Value]"),
    ("s2", "Wstore"),
    ("f2", "Wframe"),
    ("es2", "List[Einstr]"),
  ]
  for full in [false, true] {
    let vars = if full {
      malloc_entry_variables() +
      [("full_idx", "Num")] +
      model +
      [("caller", "List[Value]")]
    } else {
      malloc_entry_variables() +
      [("d", w32), ("try_idx", "Num")] +
      model.filter(x => x.0 != "d") +
      [("vs0", "List[Value]"), ("lc0", "List[Value]")]
    }
    let name = if full { "tlsf_full_malloc" } else { "tlsf_try_malloc" }
    let source = inst(
      thm(name + "_all"),
      vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
    )
    let (natives, all) = @basics.dest_imp(@kernel.concl(source))
    let t = @basics.strip_comb(all).1.to_array()
    let args = t[:3].to_owned() +
      [t[3]] +
      (if full { [t[4], t[5], t[6]] } else { [t[4], t[5]] }) +
      runvars.map(x => tm("(" + x.0 + " : " + x.1 + ")"))
    let adequate = @bool.ispecl(
      @list.List(args),
      thm(if full { "sl_abort_m_adequate" } else { "sl_triple_m_adequate" }),
    )
    let (need, result) = @basics.dest_imp(@kernel.concl(adequate))
    let assumptions = @basics.conjuncts(need).to_array()
    let pre = ([natives] + assumptions[1:].to_owned())
      .map(x => "(" + show(x) + ")")
      .join(" && ")
    let _ = lemma(
      name + "_run",
      page_quantify(vars + runvars) + pre + " → " + show(result),
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(adequate),
        @simp.asm_rewrite_tac(ths([@class.eta_ax()])),
        free_apply(source),
      ]),
    )
  }
}
