// Startup owns the zeroed unused suffix and freezes clients at the original
// memory length. Successful initialization supplies this explicit empty model.

///|
fn malloc_start_model(d : String, lim : String) -> Array[String] {
  let m = "tlsf_initialize_origin(" + d + ")"
  let hdr = "tlsf_initialize_header(" + d + "," + lim + ")"
  let nil = "(NIL : List[" + w32 + "])"
  let empty = "(p : " + w32 + ") => " + nil
  let bins = "(f : Num) => (j : Num) => " + nil
  let table = "(j : Num) => " + nil
  [
    d,
    lim,
    m,
    "[" + m + "]",
    "tlsf_initialize_headers(" + d + "," + lim + ")",
    "tlsf_push_fl(" + hdr + ",word(0))",
    "tlsf_push_sb(" + hdr + ",(f : Num) => word(0))",
    "tlsf_push_bl(" + hdr + "," + m + "," + bins + ")",
    nil,
    "(p : " + w32 + ") => (0 : Num)",
    empty,
    empty,
    empty,
    table,
    table,
  ]
}

///|
fn malloc_start_frozen() -> String {
  "(gs : List[Value]) => (ms : Num) => (fp : " + rty + ")(gs,(lim : Num))"
}

///|
fn malloc_start_initialize_native() -> String {
  "EL(sfunc_ind((inst : Inst),(initialize_idx : Num)),(fs : List[Cl])) == Func_native((inst : Inst),Tf(NIL,NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_initialize_code((d : " +
  w32 +
  "),(push : Num)))"
}

///|
fn define_tlsf_malloc_start_state() -> Unit raise {
  let args = "(d : " +
    w32 +
    "),(n : " +
    w32 +
    "),(lim : Num),(before : " +
    heap +
    "),(fp : " +
    rty +
    ")"
  let init = "tlsf_initialize_saved(d,lim,before,fp)(gs,ms,h)"
  def(
    "tlsf_malloc_start_pre",
    "tlsf_malloc_start_pre(" +
    args +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => res == [" +
    malloc_i("n") +
    "] && val(n) <= 4160749568 && tlsf_initialize_valid(d,lim) && " +
    init +
    ")",
  )
  let zero = "n == word(0) && res == [" + malloc_i("word(0)") + "] && " + init
  let success = "∃ ptr : " +
    w32 +
    ", !(n == word(0)) && res == [" +
    malloc_i("ptr") +
    "] && tlsf_malloc_result(d,n,lim,fp,ptr)(gs,ms,h)"
  let failure = "!(n == word(0)) && res == [" +
    malloc_i("word(4294967295)") +
    "] && tlsf_initialize_post(d,lim,before,fp,NIL,gs,ms,h)"
  for
    (name, body) in [
      ("try", "(" + zero + ") || (" + success + ") || (" + failure + ")"),
      ("full", "(" + zero + ") || (" + success + ")"),
    ] {
    def(
      "tlsf_" + name + "_malloc_start_post",
      "tlsf_" +
      name +
      "_malloc_start_post(" +
      args +
      ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => " +
      body +
      ")",
    )
  }
  def(
    "tlsf_malloc_start_abort",
    "tlsf_malloc_start_abort((d : " +
    w32 +
    "),(lim : Num),(before : " +
    heap +
    "),(fp : " +
    rty +
    ")) == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => tlsf_initialize_abort(d,lim,before,fp,vs,lc,gs,ms,h) || tlsf_malloc_state(d,lim,fp,gs,ms,h))",
  )
}

///|
fn prove_tlsf_malloc_start_state() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let args = malloc_start_model(d, "(ms : Num)")
  let vars = [
    ("d", w32),
    ("lim", "Num"),
    ("before", heap),
    ("fp", rty),
    ("gs", "List[Value]"),
    ("ms", "Num"),
    ("h", heap),
  ]
  let _ = startup_lemma(
    "tlsf_malloc_start_initialized",
    page_quantify(vars) +
    "tlsf_initialize_post(" +
    d +
    "," +
    lim +
    ",(before : " +
    heap +
    "),(fp : " +
    rty +
    "),NIL,gs,ms,h) == (ms == tlsf_initialize_limit(d,lim) && star(tlsf_allocator(" +
    args.join(",") +
    "),fp(gs,lim),h))",
    @simp.rewrite_tac(
      ths([
        thm("tlsf_initialize_post"),
        thm("tlsf_allocator_empty_pages"),
        thm("star_assoc"),
      ]),
    ),
  )
  for name in ["try", "full"] {
    let _ = startup_lemma(
      "tlsf_" + name + "_malloc_start_arity",
      page_quantify(vars + [("n", w32), ("res", "List[Value]")]) +
      "tlsf_" +
      name +
      "_malloc_start_post(d,n,lim,before,fp,res,gs,ms,h) → LENGTH(res) == 1",
      seq([
        @simp.rewrite_tac(ths([thm("tlsf_" + name + "_malloc_start_post")])),
        @tactics.repeat_tac(@tactics.strip_tac),
        subst_vars(),
        @simp.rewrite_tac(ths([@lists.length()])),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
      ]),
    )
  }
}
