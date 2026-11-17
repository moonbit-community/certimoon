// Partial-page allocation bypasses page reservation and TLSF.

///|
fn prove_tlsf_malloc_case_partial() -> Unit raise {
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
    let _post = "tlsf_try_malloc_post(" +
      (a + [n, "(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
      ")"
    let q = malloc_attempt_post(v, a, n)
    let code = malloc_part(v, "body")
    let export_path = @simp.rewrite_rule(ths([@words.word_val()]))(
      inst(
        thm("tlsf_malloc_" + v + "_partial_export"),
        malloc_export_arguments(v, a, n, "partial"),
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
      ") && !((p : " +
      w +
      ") == word(0))"
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
      thm("tlsf_malloc_" + v + "_fast_nil"),
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
    let partlookup = inst(
      thm("tlsf_malloc_" + v + "_partial_cons"),
      pubargs +
      a +
      [
        n,
        cls,
        "(before : " + heap + ")",
        "(fp : " + rty + ")",
        malloc_i("word(0)"),
        "(l1 : Value)",
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
        "(p : " + w + ")",
        "(z : List[" + w + "])",
      ],
    )
    let cachecode = malloc_program_code(malloc_part(v, "cached"))
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
      } else if args is Some([_, yes, _]) && malloc_code_prefix(cachecode, yes) {
        "st(NIL," +
        malloc_locals(v, [
          malloc_i("word(0)"),
          malloc_i(cls),
          "(l2 : Value)",
          "(l3 : Value)",
          "(l4 : Value)",
        ]).replace(old="(original : Value)", new=malloc_original(v, n)) +
        "," +
        r +
        ")"
      } else {
        malloc_false()
      }
    })
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_partial_case",
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
        Array::make(6, malloc_vc()),
        afters~,
        chunks=[ready, lookup, partlookup, export_path, dead],
        rws=malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
