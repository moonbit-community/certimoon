// The dispatch prefixes read metadata through persistent views.

///|
fn prove_tlsf_malloc_lookup_raw() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let n = "(n : " + w + ")"
  let kw = "(kw : " + w + ")"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let sh = "word_jshl(" + kw + ",word(3))"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let head = (k : String, fast : Bool) => {
    "tlsf_small_head(" + a[if fast { 13 } else { 14 }] + "(val(" + k + ")))"
  }
  let vars = malloc_publication_variables() +
    model +
    [
      ("n", w),
      ("kw", w),
      ("before", heap),
      ("fp", rty),
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let same = seq([gen, @tactics.repeat_tac(@tactics.strip_tac), arw([])])
  let rules = step_rules +
    [
      "st_malloc_load_fast", "st_malloc_load_partial", "st_malloc_load_top", "st_memory_size_at",
    ]
  for v in malloc_variant_names() {
    let fastLocals = (work : Array[String]) => {
      let work = work.copy()
      if v == "first" && work[0] == malloc_i(n) {
        work[0] = "(l0 : Value)"
      }
      let s = malloc_locals(v, work)
      if v == "first" {
        s.replace(old="(original : Value)", new=malloc_i(n))
      } else {
        s
      }
    }
    let _ = sym_prove(
      "tlsf_malloc_" + v + "_fast_lookup_raw",
      page_quantify(vars) +
      "val(" +
      a[0] +
      ") <= 4294965088 && val(" +
      cls +
      ") < 33 → sl_triple(st(NIL," +
      fastLocals([
        malloc_i(n),
        "(l1 : Value)",
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      ]) +
      "," +
      r +
      ")," +
      malloc_part(v, "fast_lookup") +
      ",st([" +
      malloc_i(head(cls, true)) +
      "]," +
      fastLocals([
        malloc_i(head(cls, true)),
        malloc_i(cls),
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      ]) +
      "," +
      r +
      "))",
      [],
      () => [same, same],
      rules~,
      kind="lemma",
    )
    let _ = sym_prove(
      "tlsf_malloc_" + v + "_partial_lookup_raw",
      page_quantify(vars) +
      "val(" +
      a[0] +
      ") <= 4294965088 && val(" +
      kw +
      ") < 33 → sl_triple(st(NIL," +
      malloc_locals(v, [
        "(l0 : Value)",
        malloc_i(kw),
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      ]) +
      "," +
      r +
      ")," +
      malloc_part(v, "partial_lookup") +
      ",st([" +
      malloc_i(head(kw, false)) +
      "]," +
      malloc_locals(v, [
        malloc_i(head(kw, false)),
        malloc_i(kw),
        malloc_i(sh),
        "(l3 : Value)",
        "(l4 : Value)",
      ]) +
      "," +
      r +
      "))",
      [],
      () => [same, same],
      rules~,
      kind="lemma",
    )
  }
  let _ = rw
}
