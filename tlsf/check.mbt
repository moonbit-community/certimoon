///|
let conditional_started : Ref[Bool] = Ref::{ val: false, }

///|
let checks : Ref[@logic.ProofPlan?] = Ref::{ val: None, }

///|
let prepared_until : Ref[String?] = Ref::{ val: None, }

///|
/// Prepare individual checks in a fresh process. The HOL/Wasm/core logic base
/// and TLSF definitions are checked normally; earlier TLSF lemmas become explicit
/// premises. No TLSF registered proof body runs during collection. Kernel
/// definitions persist, so use a separate process for full replay afterwards.
pub fn prepare_checks(until~ : String? = None) -> @logic.ProofPlan raise {
  if checks.val is Some(plan) {
    if (until is None && prepared_until.val is Some(_)) ||
      (until is Some(name) && !plan.names().contains(name)) {
      raise Failure(
        "certimoon/tlsf: extending a partial catalog requires a fresh process",
      )
    }
    return plan
  }
  if loaded.val || conditional_started.val {
    raise Failure("certimoon/tlsf: preparing checks requires a fresh process")
  }
  @logic.load()
  conditional_started.val = true
  let plan = @logic.collect_proofs("tlsf", build_tlsf, until~)
  checks.val = Some(plan)
  prepared_until.val = until
  plan
}

///|
/// Check one TLSF lemma assuming only earlier TLSF statements. This conditional
/// check is for development; `verify` establishes the complete theory.
pub fn check_lemma(name : String) -> @logic.LemmaCheck raise {
  prepare_checks(until=Some(name)).check(name)
}

///|
/// Full replay: execute every proof, require closed theorems, and audit axioms.
pub fn verify() -> Unit raise {
  if conditional_started.val {
    raise Failure(
      "certimoon/tlsf: full replay requires a fresh process after conditional setup",
    )
  }
  load()
  for name in names() {
    if !@kernel.hyp(thm(name)).is_empty() {
      raise Failure("certimoon/tlsf: full replay left hypotheses: " + name)
    }
  }
  @testkit.check_axioms()
}
