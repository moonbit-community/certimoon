// The guard is read-only; valid payloads fall through and null exits the block.

///|
fn prove_tlsf_public_free_control() -> Unit raise {
  let w = w32
  let gvars = malloc_g_variables()
  let env = malloc_g_env()
  let r = "(R : " + rty + ")"
  let ptr = "(ptr : " + w + ")"
  let d = "(d : " + w + ")"
  let lc0 = "[" + malloc_i(ptr) + ",(l1 : Value),(l2 : Value)]"
  let lc1 = "[" + malloc_i(ptr) + "," + malloc_i(d) + ",(l2 : Value)]"
  let vars = gvars +
    [
      ("d", w),
      ("free_idx", "Num"),
      ("ptr", w),
      ("l1", "Value"),
      ("l2", "Value"),
      ("R", rty),
    ]
  let _ = sym_prove(
    "tlsf_public_free_guard_live",
    page_quantify(vars) +
    "!word_ugt(" +
    d +
    ",word(4294965088)) && !word_ult(" +
    ptr +
    ",word_add(tlsf_base(" +
    d +
    "),word(2184))) → sl_triple_g(" +
    env +
    ",st(NIL," +
    lc0 +
    "," +
    r +
    "),tlsf_public_free_guard(d,free_idx),st(NIL," +
    lc1 +
    "," +
    r +
    "),(labels : List[" +
    sassn +
    "]))",
    [],
    () => [public_free_vc(), public_free_vc()],
    afters=["st(NIL," + lc1 + "," + r + ")"],
    kind="lemma",
  )
  let before = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (∃ l : List[Value], st([" +
    malloc_i("word(0)") +
    "],l," +
    r +
    ")(vs,lc,gs,ms,h))"
  let after = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => vs == NIL && " +
    r +
    "(gs,ms,h)"
  let _ = sym_prove(
    "tlsf_public_free_drop",
    page_quantify(gvars + [("R", rty)]) +
    "sl_triple_g(" +
    env +
    "," +
    before +
    ",[Drop]," +
    after +
    ",(labels : List[" +
    sassn +
    "]))",
    [],
    () => [public_free_vc()],
    kind="lemma",
  )
}
