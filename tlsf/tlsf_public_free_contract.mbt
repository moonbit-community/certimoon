// The public API consumes a live allocation and frames every other client.

///|
#callsite(autofill(loc))
fn public_free_def(
  name : String,
  stmt : String,
  loc~ : SourceLoc,
) -> Unit raise {
  // These contracts are nonrecursive equations; use the ordinary HOL rule.
  @logic.record(name, @drule.new_definition(tm(stmt)), kind="definition", loc~)
}

///|
fn public_free_state(a : Array[String], fp : String) -> String {
  "tlsf_public_free_state(" + [a[0], a[1], fp].join(",") + ")"
}

///|
fn public_free_r(
  a : Array[String],
  m : String,
  cap : String,
  fp : String,
) -> String {
  "(gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => ms == " +
  a[1] +
  " && " +
  small_star([
    "tlsf_allocator(" + a.join(",") + ")",
    "tlsf_bytes(val(" + m + ")+8," + cap + ")",
    "(" + fp + ")(gs,ms)",
  ]) +
  "(h)"
}

///|
fn public_free_post(a : Array[String], fp : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => vs == NIL && " +
  public_free_state(a, fp) +
  "(gs,ms,h)"
}

///|
fn define_tlsf_public_free_contract() -> Unit raise {
  let a = block_model_args()
  let fp = "(fp : " + rty + ")"
  let worlds = page_model_variables()[2:].to_owned()
  let ex = worlds.map(v => "∃ " + v.0 + " : " + v.1 + ", ").join("")
  let state = public_free_state(a, fp)
  public_free_def(
    "tlsf_public_free_state",
    state +
    " == ((gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => ms == " +
    a[1] +
    " && (" +
    ex +
    "star(tlsf_allocator(" +
    a.join(",") +
    ")," +
    fp +
    "(gs,ms),h)))",
  )
  let ptr = "(ptr : " + w32 + ")"
  let params = (a + [ptr, fp]).join(",")
  let own = "tlsf_malloc_owned(" + (a + [ptr, "(cap : Num)"]).join(",") + ")"
  let client = "(" + fp + ")((gs : List[Value]),(ms : Num))"
  let empty = "(" +
    ptr +
    " == word(0) && star(tlsf_allocator(" +
    a.join(",") +
    ")," +
    client +
    ",(h : " +
    heap +
    ")))"
  let live = "(∃ cap : Num, " +
    own +
    " && " +
    small_star([
      "tlsf_allocator(" + a.join(",") + ")",
      "tlsf_bytes(val(" + ptr + "),cap)",
      client,
    ]) +
    "(h))"
  public_free_def(
    "tlsf_public_free_pre",
    "tlsf_public_free_pre(" +
    params +
    ") == ((args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => args == [" +
    malloc_i(ptr) +
    "] && ms == " +
    a[1] +
    " && (" +
    empty +
    " || " +
    live +
    "))",
  )
  public_free_def(
    "tlsf_public_free_post",
    "tlsf_public_free_post(" +
    [a[0], a[1], fp].join(",") +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => res == NIL && " +
    state +
    "(gs,ms,h))",
  )
}

///|
fn public_free_vc(extra~ : Array[@kernel.Thm] = []) -> @tactics.Tactic raise {
  malloc_vc(
    extra=extra +
      [
        thm("tlsf_base"),
        thm("tlsf_public_free_unpayload"),
        @words.word_ult_v1(),
      ],
  )
}
