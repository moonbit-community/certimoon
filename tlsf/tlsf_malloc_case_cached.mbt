// Cached slots return before any TLSF call or page allocation is executed.

///|
fn prove_tlsf_malloc_case_cached() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  for v in malloc_variant_names() {
    let b = "(b : " + w + ")"
    let bs = "(bs : List[" + w + "])"
    let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
    let r = "tlsf_malloc_ro(" +
      (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
      ")"
    let initlc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let q = malloc_attempt_post(v, a, n)
    let code = malloc_part(v, "body")
    let export_path = @simp.rewrite_rule(ths([@words.word_val()]))(
      inst(
        thm("tlsf_malloc_" + v + "_cached_export"),
        malloc_export_arguments(v, a, n, "cached"),
      ),
    )
    let need = show(@basics.dest_imp(@kernel.concl(export_path)).0)
    let setup = inst(thm("tlsf_malloc_request_setup"), [n])
    let math = show(@basics.dest_imp(@kernel.concl(setup)).1)
    let cond = "tlsf_physical_ok(" +
      a[:5].to_owned().join(",") +
      ") && " +
      block_backing(a) +
      " && " +
      block_lists(a) +
      " && (" +
      malloc_guard_cond(a) +
      ") && (" +
      malloc_helper_natives() +
      ") && 0 < val(" +
      n +
      ") && val(" +
      n +
      ") <= 256 && !(" +
      n +
      " == word(0)) && (" +
      math +
      ") && (" +
      need +
      ") && !(" +
      b +
      " == word(0))"
    let pubargs = malloc_publication_variables().map(x => {
      if x.0 == "original" {
        malloc_original(v, n)
      } else {
        "(" + x.0 + " : " + x.1 + ")"
      }
    })
    let g = malloc_g_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    let ready = inst(
      thm("tlsf_malloc_" + v + "_ready_raw"),
      g +
      pubargs +
      a +
      [
        "(l0 : Value)",
        n,
        "(before : " + heap + ")",
        "(fp : " + rty + ")",
        "(l1 : Value)",
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      ],
    )
    let lookup = inst(
      thm("tlsf_malloc_" + v + "_fast_cons"),
      pubargs +
      a +
      [
        n,
        cls,
        "(before : " + heap + ")",
        "(fp : " + rty + ")",
        "(l0 : Value)",
        "(l1 : Value)",
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
        b,
        bs,
      ],
    )
    let dead = inst(
      thm("tlsf_malloc_" + v + "_dead_large"),
      g + malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")"),
    )
    let c = malloc_program_code(code)
    let afters = malloc_continuations(c).map(instr => {
      let args = args_of(instr, "If", 3)
      if args is Some([_, yes, _]) &&
        @basics.is_list(yes) &&
        @basics.dest_list(yes).length() == 2 &&
        head_name(@basics.dest_list(yes).head().unwrap()) == "EConstNum" {
        "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => !(" +
        n +
        " == word(0)) && st(NIL," +
        initlc +
        "," +
        r +
        ")(vs,lc,gs,ms,h)"
      } else {
        malloc_false()
      }
    })
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_cached_case",
        page_quantify(malloc_case_variables()) +
        cond +
        " → sl_triple_g((G : " +
        malloc_g_variables()[0].1 +
        "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
        (if v == "try" { q } else { "(rp : " + sassn + ")" }) +
        ",st(NIL," +
        initlc +
        "," +
        r +
        ")," +
        code +
        "," +
        q +
        ",[" +
        q +
        "])",
        [],
        Array::make(5, malloc_vc()),
        afters~,
        chunks=[ready, lookup, export_path, dead],
        rws=malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
