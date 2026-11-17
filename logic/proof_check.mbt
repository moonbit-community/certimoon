// Conditional development checks. Assumptions live only in this scoped catalog;
// they are never installed in the normal, fully verified theorem registry.

///|
priv struct ProofDeclaration {
  name : String
  goal : @kernel.Term
  th : @kernel.Thm
  kind : String
  loc : String
  proof : (() -> @kernel.Thm raise)?
}

///|
/// An ordered catalog of real definitions and lazy proof declarations.
struct ProofPlan {
  declarations : Array[ProofDeclaration]
  indices : Map[String, Int32]
  premises : Map[@kernel.Term, Int32]
}

///|
priv struct ProofContext {
  plan : ProofPlan
  // None collects declarations; Some(i) checks declaration i using only < i.
  target : Int32?
  until : String?
  types : Ref[Array[@kernel.HolType]?]
  instances : Array[(@kernel.Thm, Array[@kernel.Thm])]
}

///|
fn proof_scope(
  plan : ProofPlan,
  target : Int32?,
  until : String?,
) -> ProofContext {
  { plan, target, until, types: Ref::{ val: None, }, instances: [], }
}

///|
priv suberror ProofCollected {
  ProofCollected
}

///|
let proof_context : Ref[ProofContext?] = Ref::{ val: None, }

///|
/// A successful conditional check. `theorem()` is a closed implication whose
/// antecedents are the actual premises used, rather than an unchecked lemma.
struct LemmaCheck {
  name : String
  statement : @kernel.Term
  conditional : @kernel.Thm
  premises : Array[String]
}

///|
pub fn LemmaCheck::name(self : LemmaCheck) -> String {
  self.name
}

///|
pub fn LemmaCheck::statement(self : LemmaCheck) -> @kernel.Term {
  self.statement
}

///|
pub fn LemmaCheck::theorem(self : LemmaCheck) -> @kernel.Thm {
  self.conditional
}

///|
pub fn LemmaCheck::premises(self : LemmaCheck) -> Array[String] {
  self.premises.copy()
}

///|
/// Whether declaration collection or an individual conditional check is active.
pub fn checking_proof() -> Bool {
  proof_context.val is Some(_)
}

///|
fn ProofPlan::insert(self : ProofPlan, d : ProofDeclaration) -> Unit raise {
  if self.indices.contains(d.name) || thms.contains(d.name) {
    raise Failure("certimoon/logic: duplicate proof declaration " + d.name)
  }
  let index = self.declarations.length()
  self.indices[d.name] = index
  if d.proof is Some(_) && !self.premises.contains(d.goal) {
    self.premises[d.goal] = index
  }
  self.declarations.push(d)
}

///|
fn conditional_record(
  name : String,
  th : @kernel.Thm,
  kind : String,
  loc : SourceLoc,
) -> Bool {
  guard proof_context.val is Some(ctx) else { return false }
  if ctx.target is None {
    if (kind != "definition" && kind != "program") ||
      !@kernel.hyp(th).is_empty() {
      abort("certimoon/logic: proof must be declared lazily: " + name)
    }
    ctx.plan.insert({
      name,
      goal: @kernel.concl(th),
      th,
      kind,
      loc: loc.to_string(),
      proof: None,
    }) catch {
      e => abort(e.to_string())
    }
  }
  // During a check, recording a result must not publish a conditional theorem.
  true
}

///|
fn conditional_thm(name : String) -> @kernel.Thm? {
  guard proof_context.val is Some(ctx) else { return None }
  ctx.lookup(name) catch {
    e => abort(e.to_string())
  }
}

///|
fn ProofContext::lookup(
  self : ProofContext,
  name : String,
) -> @kernel.Thm? raise {
  guard self.plan.indices.get(name) is Some(i) else { return None }
  if self.target is Some(target) && i >= target {
    raise Failure(
      "certimoon/logic: self/forward reference while checking: " + name,
    )
  }
  Some(self.plan.declarations[i].th)
}

///|
/// Collect statements without executing their proof builders. The caller must
/// use a fresh theory: kernel definitions cannot be rolled back after a failure.
pub fn collect_proofs(
  pkg : String,
  build : () -> Unit raise,
  until~ : String? = None,
) -> ProofPlan raise {
  load()
  if checking_proof() || in_load.val {
    raise Failure("certimoon/logic: cannot nest proof collection")
  }
  let plan : ProofPlan = {
    declarations: [],
    indices: Map([]),
    premises: Map([]),
  }
  proof_context.val = Some(proof_scope(plan, None, until))
  @theory.begin_theory(pkg)
  defer {
    proof_context.val = None
    @theory.end_theory()
  }
  build() catch {
    ProofCollected => ()
    e => raise e
  }
  if until is Some(name) && !plan.indices.contains(name) {
    raise Failure("certimoon/logic: unknown proof " + name)
  }
  plan
}

///|
/// Declare a statement and its lazy proof. In full replay the builder runs
/// normally. In a conditional catalog the kernel's assumption rule supplies the
/// statement as an explicit hypothesis, without introducing a new axiom.
#callsite(autofill(loc))
pub fn declare_proof(
  name : String,
  goal : @kernel.Term,
  proof : () -> @kernel.Thm raise,
  kind~ : String = "lemma",
  loc~ : SourceLoc,
) -> @kernel.Thm raise {
  guard proof_context.val is Some(ctx) else {
    let th = proof()
    if !@kernel.hyp(th).is_empty() || !@basics.aconv(@kernel.concl(th), goal) {
      raise Failure("certimoon/logic: invalid full proof declaration: " + name)
    }
    return th
  }
  if ctx.target is Some(_) {
    raise Failure("certimoon/logic: cannot declare a proof inside a check")
  }
  let th = @kernel.assume_rule(goal)
  ctx.plan.insert({
    name,
    goal,
    th,
    kind,
    loc: loc.to_string(),
    proof: Some(proof),
  })
  if ctx.until == Some(name) {
    raise ProofCollected
  }
  th
}

///|
/// Like HOL Light's `prove`, except a scoped individual check may retain its
/// explicit premises. Full replay still rejects every additional hypothesis.
pub fn prove(goal : @kernel.Term, tac : @tactics.Tactic) -> @kernel.Thm raise {
  if !checking_proof() {
    return @tactics.prove(goal, tac)
  }
  let th = @tactics.tac_proof((@list.List([]), goal), tac)
  if @kernel.concl(th) == goal {
    th
  } else {
    @kernel.eq_mp(@equal.alpha_rule(@kernel.concl(th), goal), th)
  }
}

///|
/// Names with proof bodies, in dependency order (definitions are excluded).
pub fn ProofPlan::names(self : ProofPlan) -> Array[String] {
  self.declarations.filter(d => d.proof is Some(_)).map(d => d.name)
}

///|
/// The source location of a declaration.
pub fn ProofPlan::location(self : ProofPlan, name : String) -> String? {
  self.indices.get(name).map(i => self.declarations[i].loc)
}

///|
/// The listing kind of a declaration (lemma, example, definition, or program).
pub fn ProofPlan::kind(self : ProofPlan, name : String) -> String? {
  self.indices.get(name).map(i => self.declarations[i].kind)
}

///|
fn add_schema_type(
  ty : @kernel.HolType,
  seen : Map[@kernel.HolType, Bool],
  out : Array[@kernel.HolType],
) -> Unit {
  if seen.contains(ty) {
    return
  }
  seen[ty] = true
  out.push(ty)
  if ty is @kernel.Tyapp(_, args) {
    for arg in args {
      add_schema_type(arg, seen, out)
    }
  }
}

///|
fn add_schema_term_types(
  term : @kernel.Term,
  seen : Map[@kernel.HolType, Bool],
  out : Array[@kernel.HolType],
) -> Unit {
  match term {
    @kernel.Var(_, ty) | @kernel.Const(_, ty) => add_schema_type(ty, seen, out)
    @kernel.Comb(f, x) | @kernel.Abs(f, x) => {
      add_schema_term_types(f, seen, out)
      add_schema_term_types(x, seen, out)
    }
  }
}

///|
fn ProofContext::schema_types(self : ProofContext) -> Array[@kernel.HolType] {
  if self.types.val is Some(types) {
    return types
  }
  let types = []
  let seen : Map[@kernel.HolType, Bool] = Map([])
  let limit = self.target.unwrap_or(self.plan.declarations.length() - 1)
  for i = 0; i <= limit; i = i + 1 {
    add_schema_term_types(self.plan.declarations[i].goal, seen, types)
  }
  // Collection still grows; only cache the complete prefix during a check.
  if self.target is Some(_) {
    self.types.val = Some(types)
  }
  types
}

///|
// HOL's PART_MATCH deliberately rejects any instantiation of hypotheses.
// Specialize conditional polymorphic premises before passing them to standard
// rewrite tactics. Every resulting hypothesis remains explicit and is audited
// against earlier schemas at the check boundary. Closed theorems are unchanged.
fn conditional_instances(xs : Array[@kernel.Thm]) -> Array[@kernel.Thm] {
  guard proof_context.val is Some(ctx) else { return xs }
  let out = []
  for th in xs {
    if @kernel.hyp(th).is_empty() {
      out.push(th)
      continue
    }
    let variables = @kernel.type_vars_in_term(@kernel.concl(th)).to_array()
    if variables.is_empty() {
      out.push(th)
      continue
    }
    let mut cached : Array[@kernel.Thm]? = None
    for (original, instances) in ctx.instances {
      if original == th {
        cached = Some(instances)
        break
      }
    }
    if cached is Some(instances) {
      out.append(instances)
      continue
    }
    let mut instances = [th]
    for variable in variables {
      let next = []
      for candidate in instances {
        for ty in ctx.schema_types() {
          next.push(@kernel.inst_type(@list.List([(ty, variable)]), candidate))
        }
      }
      instances = next
    }
    ctx.instances.push((th, instances))
    out.append(instances)
  }
  out
}

///|
/// Matching modus ponens with explicit type specialization of a conditional
/// premise. The ordinary tactic still checks the match and reconstructs proof.
pub fn match_mp_tac(th : @kernel.Thm) -> @tactics.Tactic raise {
  if !checking_proof() || @kernel.hyp(th).is_empty() {
    return @tactics.match_mp_tac(th)
  }
  let body = @basics.strip_forall(@kernel.concl(th)).1
  let consequence = @basics.dest_imp(body).1
  g => {
    let inst = @drule.term_match(@list.List([]), consequence, g.1)
    @tactics.match_mp_tac(@kernel.inst_type(inst.2, th))(g)
  }
}

///|
fn ProofPlan::premise_index(
  self : ProofPlan,
  hyp : @kernel.Term,
  limit : Int32,
) -> Int32? raise {
  if self.premises.get(hyp) is Some(i) && i < limit {
    return Some(i)
  }
  // Rules may instantiate free term/type variables or rename bound variables.
  // Accept only an actual instance of an earlier lemma's complete statement.
  let mut fallback : Int32? = None
  for i = 0; i < limit; i = i + 1 {
    let d = self.declarations[i]
    if d.proof is None {
      continue
    }
    let inst = Some(@drule.term_match(@list.List([]), d.goal, hyp)) catch {
      _ => None
    }
    if inst is Some(inst) &&
      @basics.aconv(@drule.instantiate(inst, d.goal), hyp) {
      if @basics.aconv(@kernel.inst(inst.2, d.goal), hyp) {
        return Some(i)
      }
      if fallback is None {
        fallback = Some(i)
      }
    }
  }
  fallback
}

///|
/// Run exactly one registered proof against earlier lemma premises. The result
/// exposes a closed implication; no conditional result enters `thm`/`names`.
pub fn ProofPlan::check(self : ProofPlan, name : String) -> LemmaCheck raise {
  if checking_proof() || in_load.val {
    raise Failure("certimoon/logic: cannot nest an individual proof check")
  }
  guard self.indices.get(name) is Some(index) else {
    raise Failure("certimoon/logic: unknown proof " + name)
  }
  let d = self.declarations[index]
  guard d.proof is Some(build) else {
    raise Failure("certimoon/logic: a definition is not a lemma: " + name)
  }
  proof_context.val = Some(proof_scope(self, Some(index), None))
  defer {
    proof_context.val = None
  }
  if trace.val {
    println("checking " + name)
  }
  let th = build()
  if trace.val {
    println("checking premises of " + name)
  }
  if !@basics.aconv(@kernel.concl(th), d.goal) {
    raise Failure(
      "certimoon/logic: proof returned the wrong conclusion: " + name,
    )
  }
  let used : Array[String] = []
  for h in @kernel.hyp(th) {
    guard self.premise_index(h, index) is Some(i) else {
      raise Failure(
        "certimoon/logic: unapproved premise in " + name + ": " + show(h),
      )
    }
    let premise = self.declarations[i].name
    if !used.contains(premise) {
      used.push(premise)
    }
  }
  { name, statement: d.goal, conditional: @bool.disch_all(th), premises: used, }
}
