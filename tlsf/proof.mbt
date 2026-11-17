// Shared proof tactics and syntax come from the core logic.

///|
using @logic {
  args_of,
  arith,
  beta_goal,
  body_post,
  body_pre,
  call_free_tac,
  call_post,
  call_pre,
  def,
  have,
  head_name,
  heap,
  hprop,
  intro_tac,
  norm_conv,
  pre_conv,
  program,
  rty,
  sassn,
  section,
  seq,
  show,
  show_goal,
  solve,
  split_conjs,
  step_rules,
  subst_only,
  subst_vars,
  ths,
  tm,
  triple_l_terms,
  use_eqs,
  w32,
}

///|
// Keep the statements eager and the proof bodies lazy in both verification
// modes. Full replay calls the same builders with genuinely proved predecessors.
#callsite(autofill(loc))
fn lemma(
  name : String,
  stmt : String,
  tactic : () -> @tactics.Tactic raise,
  kind~ : String = "lemma",
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  let goal = tm(stmt)
  @logic.declare_proof(
    name,
    goal,
    fn() raise { @logic.lemma_term(name, goal, tactic(), kind~, loc~) },
    kind~,
    loc~,
  )
}

///|
#callsite(autofill(loc))
fn derived(
  name : String,
  stmt : String,
  proof : () -> @kernel.Thm raise,
  kind~ : String = "lemma",
  loc~ : SourceLoc,
) -> Unit raise {
  let goal = tm(stmt)
  ignore(
    @logic.declare_proof(
      name,
      goal,
      fn() raise {
        let th = proof()
        @logic.record(name, th, kind~, loc~)
        th
      },
      kind~,
      loc~,
    ),
  )
}

///|
#callsite(autofill(loc))
fn sym_prove(
  name : String,
  stmt : String,
  invs : Array[String],
  vcs : () -> Array[@tactics.Tactic] raise,
  afters~ : Array[String] = [],
  rules~ : Array[String] = step_rules,
  chunks~ : Array[@kernel.Thm] = [],
  rws~ : Array[@kernel.Thm] = [],
  specs~ : Array[@kernel.Thm] = [],
  calls~ : Array[(Int32, Array[String])] = [],
  kind~ : String = "example",
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  let goal = tm(stmt)
  @logic.declare_proof(
    name,
    goal,
    fn() raise {
      @logic.sym_prove_term(
        name,
        goal,
        invs,
        vcs(),
        afters~,
        rules~,
        chunks~,
        rws~,
        specs~,
        calls~,
        kind~,
        loc~,
      )
    },
    kind~,
    loc~,
  )
}
