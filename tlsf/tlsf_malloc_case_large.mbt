// The large-request branch calls the compiled take function once.

///|
fn prove_tlsf_malloc_case_large(after_initialize~ : Bool = false) -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  for
    v in (if after_initialize {
      ["try", "first"]
    } else {
      malloc_variant_names()
    }) {
    let initlc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let q = malloc_attempt_post(v, a, n)
    let code = malloc_part(v, if after_initialize { "resume" } else { "body" })
    let slot = "word_add(word_and(word_add(" +
      a[0] +
      ",word(15)),word(4294967280)),word(1908))"
    let readylc = if after_initialize {
      initlc
    } else {
      malloc_locals(
        v,
        if v == "first" {
          [
            malloc_i(slot),
            "(l1 : Value)",
            "(l2 : Value)",
            "(l3 : Value)",
            "(l4 : Value)",
          ]
        } else {
          [
            malloc_i(n),
            malloc_i(slot),
            "(l2 : Value)",
            "(l3 : Value)",
            "(l4 : Value)",
          ]
        },
      ).replace(old="(original : Value)", new=malloc_original(v, n))
    }
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
    let take = inst(
      thm("tlsf_malloc_take_call_g"),
      g +
      ["(pop : Num)", "(push : Num)", "(take_idx : Num)"] +
      a +
      [n, "(before : " + heap + ")", "(fp : " + rty + ")", readylc],
    )
    let dead = inst(
      thm("tlsf_malloc_" + v + "_dead_small"),
      g + malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")"),
    )
    let cond = "tlsf_physical_ok(" +
      a[:5].to_owned().join(",") +
      ") && " +
      block_backing(a) +
      " && (" +
      malloc_guard_cond(a) +
      ") && (" +
      malloc_helper_natives() +
      ") && 256 < val(" +
      n +
      ") && val(" +
      n +
      ") <= 4160749568 && !(" +
      n +
      " == word(0)) && !word_ugt(" +
      n +
      ",word(4160749568))"
    let afters = malloc_continuations(malloc_program_code(code)).map(instr => {
      if args_of(instr, "If", 3) is Some([_, yes, _]) &&
        @basics.dest_list(yes).length() == 2 &&
        head_name(@basics.dest_list(yes).head().unwrap()) == "EConstNum" {
        "st(NIL," + initlc + "," + r + ")"
      } else if args_of(instr, "If", 3) is Some([_, yes, _]) &&
        @basics.dest_list(yes).length() == 1 &&
        head_name(@basics.dest_list(yes).head().unwrap()) == "Unreachable" {
        "st(NIL," + readylc + "," + r + ")"
      } else {
        malloc_false()
      }
    })
    ignore(
      sym_prove(
        "tlsf_malloc_" +
        v +
        (if after_initialize { "_resume" } else { "" }) +
        "_large_case",
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
        () => Array::make(if after_initialize { 3 } else { 4 }, malloc_vc()),
        afters~,
        chunks=[ready, take, dead],
        rws=malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
