// Entry contracts freeze the client frame at the original memory size.
// Allocation transfers an exclusive payload and records its live allocator handle.

///|
fn malloc_frame(a : Array[String], fp : String, before : String) -> String {
  "(gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => ms == " +
  a[1] +
  " && " +
  (if before == "" { "" } else { "h == " + before + " && " }) +
  "star(tlsf_allocator(" +
  a.join(",") +
  "),(" +
  fp +
  ")(gs," +
  a[1] +
  "),h)"
}

///|
fn malloc_available(a : Array[String], n : String) -> String {
  let k = "DIV(val(" + n + ")+7,8)"
  let query = (r : String) => {
    "tlsf_search(" + r + "," + a[5] + "," + a[6] + "," + a[7] + ")"
  }
  "(" +
  n +
  " == word(0) || (val(" +
  n +
  ") <= 256 && (!(" +
  a[13] +
  "(" +
  k +
  ") == NIL) || !(" +
  a[14] +
  "(" +
  k +
  ") == NIL) || !(" +
  query("(word(1080) : " + w32 + ")") +
  " == word(0)))) || (256 < val(" +
  n +
  ") && !(" +
  query(n) +
  " == word(0))))"
}

///|
fn define_tlsf_malloc_contract() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let rest = model[2:].to_owned()
  let ex = rest.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("")
  let oldlim = "(oldlim : Num)"
  let fp = "(fp : " + rty + ")"
  let client = "(" + fp + ")((gs : List[Value])," + oldlim + ")"
  let now = a.copy()
  now[1] = "(ms : Num)"
  let allocator = "tlsf_allocator(" + now.join(",") + ")"
  let params = "(d : " + w + "),(n : " + w + ")," + oldlim + "," + fp
  let ptr = "(ptr : " + w + ")"
  let cap = "(cap : Num)"
  def(
    "tlsf_malloc_owned",
    "tlsf_malloc_owned(" +
    a.join(",") +
    "," +
    ptr +
    "," +
    cap +
    ") == ((∃ m : " +
    w +
    ", MEM(m," +
    a[3] +
    ") && !MEM(m," +
    a[8] +
    ") && tlsf_used(" +
    a[4] +
    "(m)) && ptr == word_add(m,word(8)) && cap == val(tlsf_size(" +
    a[4] +
    "(m)))) || (∃ p : " +
    w +
    ", ∃ b : " +
    w +
    ", MEM(p," +
    a[8] +
    ") && MEM(b," +
    a[12] +
    "(p)) && ptr == word_add(b,word(8)) && cap == " +
    a[9] +
    "(p)))",
  )
  let pure = "!(" +
    ptr +
    " == word(0)) && !(" +
    ptr +
    " == word(4294967295)) && val((n : " +
    w +
    ")) <= " +
    cap +
    " && val(" +
    ptr +
    ")+" +
    cap +
    " <= (ms : Num) && " +
    oldlim +
    " <= (ms : Num)"
  def(
    "tlsf_malloc_result",
    "tlsf_malloc_result(" +
    params +
    "," +
    ptr +
    ") == ((gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => " +
    ex +
    "∃ cap : Num, " +
    pure +
    " && tlsf_malloc_owned(" +
    now.join(",") +
    "," +
    ptr +
    "," +
    cap +
    ") && " +
    small_star(["tlsf_bytes(val(" + ptr + ")," + cap + ")", allocator, client]) +
    "(h))",
  )
}

///|
fn define_tlsf_malloc_outcome_contract() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let rest = model[2:].to_owned()
  let ex = rest.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("")
  let oldlim = "(oldlim : Num)"
  let fp = "(fp : " + rty + ")"
  let client = "(" + fp + ")((gs : List[Value])," + oldlim + ")"
  let now = a.copy()
  now[1] = "(ms : Num)"
  let allocator = "tlsf_allocator(" + now.join(",") + ")"
  let _params = "(d : " + w + "),(n : " + w + ")," + oldlim + "," + fp
  let ptr = "(ptr : " + w + ")"
  let _cap = "(cap : Num)"
  def(
    "tlsf_malloc_state",
    "tlsf_malloc_state((d : " +
    w +
    ")," +
    oldlim +
    "," +
    fp +
    ") == ((gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => " +
    oldlim +
    " <= ms && (" +
    ex +
    "star(" +
    allocator +
    "," +
    client +
    ",h)))",
  )
  let vars = model + [("n", w), ("before", heap), ("fp", rty)]
  let av = page_arguments(vars)
  let n = "(n : " + w + ")"
  let pre = "res == [" +
    malloc_i(n) +
    "] && val(" +
    n +
    ") <= 4160749568 && (" +
    malloc_frame(a, fp, "(before : " + heap + ")") +
    ")(gs,ms,h)"
  let unchanged = "(ms : Num) == " +
    a[1] +
    " && (h : " +
    heap +
    ") == (before : " +
    heap +
    ") && star(tlsf_allocator(" +
    a.join(",") +
    "),(" +
    fp +
    ")(gs," +
    a[1] +
    "),h)"
  let zero = n +
    " == word(0) && res == [" +
    malloc_i("word(0)") +
    "] && (" +
    unchanged +
    ")"
  let success = "∃ ptr : " +
    w +
    ", !(" +
    n +
    " == word(0)) && res == [" +
    malloc_i(ptr) +
    "] && tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    a[1] +
    "," +
    fp +
    "," +
    ptr +
    ")(gs,ms,h)"
  let failure = "!" +
    malloc_available(a, n) +
    " && res == [" +
    malloc_i("word(4294967295)") +
    "] && (" +
    unchanged +
    ")"
  def(
    "tlsf_try_malloc_pre",
    "tlsf_try_malloc_pre(" +
    av +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => " +
    pre +
    ")",
  )
  def(
    "tlsf_try_malloc_post",
    "tlsf_try_malloc_post(" +
    av +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (" +
    zero +
    ") || (" +
    failure +
    ") || (" +
    malloc_available(a, n) +
    " && (" +
    success +
    ")))",
  )
  def(
    "tlsf_full_malloc_post",
    "tlsf_full_malloc_post(" +
    av +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (" +
    zero +
    ") || (" +
    success +
    "))",
  )
}
