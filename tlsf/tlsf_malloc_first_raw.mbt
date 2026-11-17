// Local word triples keep every existing client assertion in the frame.

///|
fn prove_tlsf_malloc_first_publish_raw() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((" + x + " : " + w + ")))"
  let at = (x : String, n : Int32) => {
    "word_add((" + x + " : " + w + "),word(" + n.to_string() + "))"
  }
  let cell = (a : String, x : String) => {
    "pts(val((" + a + " : " + w + ")),serialise_i32((" + x + " : " + w + ")))"
  }
  let own = (xs : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(xs + ["(fp : " + rty + ")(gs,ms)"])
  }
  let base = "word_and(word_add((d : " + w + "),word(15)),word(4294967280))"
  let table = (n : Int32) => {
    "word_add(word_add((s : " +
    w +
    "),word_add(" +
    base +
    ",word(" +
    n.to_string() +
    "))),word(0))"
  }
  let ft = "word_add((s : " + w + "),word_add(" + base + ",word(1912)))"
  let pt = "word_add(word_add((s : " + w + ")," + base + "),word(1916))"
  let vc = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.asm_rewrite_tac(
      ths([
        thm("star_assoc"),
        thm("star_comm"),
        thm("star_left_comm"),
        thm("star_emp_hr"),
        thm("star_emp_hl"),
      ]),
    ),
  ])
  let env = page_quantify(malloc_publication_variables()) +
    "∀ d : " +
    w +
    ", ∀ p : " +
    w +
    ", ∀ b : " +
    w +
    ", ∀ s : " +
    w +
    ", ∀ total : " +
    w +
    ", ∀ used : " +
    w +
    ", ∀ nx : " +
    w +
    ", ∀ oldfast : " +
    w +
    ", ∀ l1 : Value, ∀ l3 : Value, ∀ l4 : Value, ∀ fp : " +
    rty
  let before = [
    cell(at("p", 12), "total"),
    cell(at("p", 16), "used"),
    cell(at("p", 20), "b"),
    cell(at("b", 8), "nx"),
    cell(ft, "oldfast"),
  ]
  let after = [
    cell(at("p", 12), "total"),
    cell(at("p", 16), "total"),
    cell(at("p", 20), "word(0)"),
    cell(at("b", 8), "word(0)"),
    cell(ft, "nx"),
  ]
  ignore(
    sym_prove(
      "tlsf_malloc_first_publish_fresh_raw",
      env +
      ", sl_triple(st(NIL,[(original : Value)," +
      i("p") +
      "," +
      i("b") +
      "," +
      i("s") +
      "," +
      i(at("p", 20)) +
      ",l4]," +
      own(before) +
      "),tlsf_malloc_first_fresh(d,initialize_idx,page_idx,take_idx,ensure_idx),st([" +
      i(at("b", 8)) +
      "],[(original : Value)," +
      i("p") +
      "," +
      i(at("b", 8)) +
      "," +
      i("s") +
      "," +
      i(at("p", 20)) +
      "," +
      i("nx") +
      "]," +
      own(after) +
      "))",
      [],
      () => [vc],
      kind="lemma",
    ),
  )
  for nonempty in [false, true] {
    let np = if nonempty {
      "(nextp : " + w + ")"
    } else {
      "(word(0) : " + w + ")"
    }
    let pre = before +
      [cell(at("p", 28), np), cell(pt, "p")] +
      (if nonempty { [cell(at(np, 24), "p")] } else { [] })
    let post = after +
      [cell(at("p", 28), np), cell(pt, np)] +
      (if nonempty { [cell(at(np, 24), "word(0)")] } else { [] })
    let lc = "[(original : Value)," +
      i(np) +
      "," +
      i("b") +
      "," +
      i("s") +
      "," +
      i(at("p", 20)) +
      "," +
      i("nx") +
      "]"
    let mid = "st(NIL," + lc + "," + own(post) + ")"
    ignore(
      sym_prove(
        "tlsf_malloc_first_publish_partial_" +
        (if nonempty { "cons" } else { "nil" }) +
        "_raw",
        env +
        ", ∀ nextp : " +
        w +
        ", " +
        (if nonempty { "!(nextp == word(0)) → " } else { "" }) +
        "sl_triple(st(NIL,[(original : Value)," +
        i("p") +
        ",l1," +
        i("s") +
        ",l3,l4]," +
        own(pre) +
        "),tlsf_malloc_first_partial(d,initialize_idx,page_idx,take_idx,ensure_idx),st([" +
        i(at("b", 8)) +
        "]," +
        lc +
        "," +
        own(post) +
        "))",
        [],
        () => [vc],
        afters=[mid],
        kind="lemma",
      ),
    )
  }
  ignore(
    sym_prove(
      "tlsf_malloc_first_publish_head_raw",
      env +
      ", sl_triple(st(NIL,[(original : Value)," +
      i("p") +
      ",l1," +
      i("s") +
      ",l3,l4]," +
      own([cell(at("p", 20), "b")]) +
      "),tlsf_malloc_first_head(d,initialize_idx,page_idx,take_idx,ensure_idx),st([" +
      i("b") +
      "],[(original : Value)," +
      i("p") +
      "," +
      i("b") +
      "," +
      i("s") +
      "," +
      i(at("p", 20)) +
      ",l4]," +
      own([cell(at("p", 20), "b")]) +
      "))",
      [],
      () => [vc],
      kind="lemma",
    ),
  )
  let _ = table
}
