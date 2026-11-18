// Both class lists are empty: reserve a page and publish its first slot,
// or propagate the exact no-fit result without changing the heap.

///|
fn prove_tlsf_malloc_case_fresh(after_initialize~ : Bool = false) -> Unit raise {
  let w = w32
  let a = block_model_args()
  let next = malloc_fresh_args(a)
  let n = "(n : " + w + ")"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let size = "8*val(" + cls + ")"
  let before = "(before : " + heap + ")"
  let fp = "(fp : " + rty + ")"
  let r = "tlsf_malloc_ro(" + (a + [before, fp]).join(",") + ")"
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : List[" + w + "])"
  let math = show(
    @basics.dest_imp(@kernel.concl(inst(thm("tlsf_malloc_request_setup"), [n]))).1,
  )
  let query = "tlsf_search((word(1080) : " +
    w +
    ")," +
    a[5] +
    "," +
    a[6] +
    "," +
    a[7] +
    ")"
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
    ") && val(" +
    a[0] +
    ") <= 4294965088 && " +
    a[13] +
    "(val(" +
    cls +
    ")) == NIL && " +
    a[14] +
    "(val(" +
    cls +
    ")) == NIL"
  for
    v in (if after_initialize {
      ["try", "first"]
    } else {
      malloc_variant_names()
    }) {
    let pubargs = malloc_publication_variables().map(x => {
      if x.0 == "original" {
        malloc_original(v, n)
      } else {
        "(" + x.0 + " : " + x.1 + ")"
      }
    })
    let g = malloc_g_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    let lc = (third : String) => {
      malloc_locals(v, [
        malloc_i("word(0)"),
        malloc_i(cls),
        third,
        "(l3 : Value)",
        "(l4 : Value)",
      ]).replace(old="(original : Value)", new=malloc_original(v, n))
    }
    let initlc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let q = malloc_attempt_post(v, a, n)
    let ready = inst(
      thm("tlsf_malloc_" + v + "_ready_raw"),
      g +
      pubargs +
      a +
      [
        "(l0 : Value)", n, before, fp, "(l1 : Value)", "(l2 : Value)", "(l3 : Value)",
        "(l4 : Value)",
      ],
    )
    let lookargs = pubargs +
      a +
      [
        n, cls, before, fp, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)",
        "(l4 : Value)", b, bs,
      ]
    let fast = inst(thm("tlsf_malloc_" + v + "_fast_nil"), lookargs)
    let partargs = lookargs.copy()
    partargs[24] = malloc_i("word(0)")
    let partial = inst(thm("tlsf_malloc_" + v + "_partial_nil"), partargs)
    let page = inst(
      thm("tlsf_malloc_" + v + "_page_shift_call_g"),
      g +
      ["(pop : Num)", "(push : Num)", "(take_idx : Num)", "(page_idx : Num)"] +
      a +
      [cls, before, fp, malloc_original(v, n), "(l3 : Value)", "(l4 : Value)"],
    )
    let head = inst(
      thm("tlsf_malloc_" + v + "_fresh_head"),
      pubargs +
      next +
      [
        p,
        b,
        bs,
        size,
        "(i : Num)",
        "(used0 : " + w + ")",
        "(prev0 : " + w + ")",
        fp,
        malloc_i(cls),
        "(l3 : Value)",
        "(l4 : Value)",
      ],
    )
    let exargs = malloc_export_arguments(v, next, n, "fresh").map(x => {
      x.replace(old="(s : Num)", new="(" + size + ")")
    })
    let export_path = inst(thm("tlsf_malloc_" + v + "_fresh_export"), exargs)
    let dead = inst(
      thm("tlsf_malloc_" + v + "_dead_large"),
      g + malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")"),
    )
    let code = malloc_part(v, if after_initialize { "resume" } else { "body" })
    let cachedcode = malloc_program_code(malloc_part(v, "cached"))
    let partialcode = malloc_program_code(malloc_part(v, "partial"))
    let headcode = malloc_program_code(malloc_part(v, "head"))
    let afters = malloc_continuations(malloc_program_code(code)).map(instr => {
      if args_of(instr, "If", 3) is Some([_, yes, _]) {
        if @basics.dest_list(yes).length() == 2 &&
          head_name(@basics.dest_list(yes).head().unwrap()) == "EConstNum" {
          "st(NIL," + initlc + "," + r + ")"
        } else if malloc_code_prefix(cachedcode, yes) {
          "st(NIL," + lc("(l2 : Value)") + "," + r + ")"
        } else if malloc_code_prefix(partialcode, yes) {
          "st(NIL," + lc(malloc_i("word(" + size + ")")) + "," + r + ")"
        } else if malloc_code_prefix(headcode, yes) {
          "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
          heap +
          ") => " +
          query +
          " == word(0) && st(NIL," +
          lc(malloc_i("word(" + size + ")")) +
          "," +
          r +
          ")(vs,lc,gs,ms,h)"
        } else {
          malloc_false()
        }
      } else {
        malloc_false()
      }
    })
    ignore(
      sym_prove(
        "tlsf_malloc_" +
        v +
        (if after_initialize { "_resume" } else { "" }) +
        "_fresh_case",
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
        () => Array::make(if after_initialize { 10 } else { 11 }, malloc_vc()),
        afters~,
        chunks=[ready, fast, partial, page, head, export_path, dead],
        rws=malloc_extra_rewrites(),
        kind="lemma",
      ),
    )
  }
}
