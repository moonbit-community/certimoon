// The compiled publication stores on one page, framed by all unrelated
// allocator and client bytes. Only the chosen payload becomes client-owned.

///|
fn prove_tlsf_malloc_retry_publish_page() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let s = "(s : Num)"
  let bs = "(bs : " + lw + ")"
  let live = "(live : " + lw + ")"
  let cap = "(cap : Num)"
  let d = "(d : " + w + ")"
  let zero = "(word(0) : " + w + ")"
  let total = "tlsf_small_total(" + s + ")"
  let cell = (a : String, x : String) => {
    "pts(" + a + ",serialise_i32((" + x + " : " + w + ")))"
  }
  let pc = (off : Int32, x : String) => {
    cell("val(" + p + ")+" + off.to_string(), x)
  }
  let i32 = (x : String) => "V_num(ConstInt32((" + x + " : " + w + ")))"
  let pb = "word_add(" + b + ",word(8))"
  let p20 = "word_add(" + p + ",word(20))"
  let ft = "val(tlsf_base(" + d + "))+1912+" + s
  let pt = "val(tlsf_base(" + d + "))+1916+" + s
  let own = (xs : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(xs + ["(fp : " + rty + ")(gs,ms)"])
  }
  let args = ["(lim : Num)", p, cap, s, b, bs, live, "(i : Num)"]
  let ready = "tlsf_small_page_ok(" +
    [
      "(lim : Num)",
      p,
      cap,
      s,
      "CONS(" + b + "," + bs + ")",
      "(NIL : " + lw + ")",
      live,
    ].join(",") +
    ")"
  let cond = "val(" +
    d +
    ") <= 4294965088 && " +
    ready +
    " && (i : Num) < " +
    total +
    " && b == tlsf_small_slot(p,s,i)"
  let old = "tlsf_small_page_heap(" +
    [p, cap, s, "CONS(" + b + "," + bs + ")", "(NIL : " + lw + ")", live].join(
      ",",
    ) +
    ")"
  let newer = "tlsf_small_page_heap(" +
    [p, cap, s, "(NIL : " + lw + ")", bs, "CONS(" + b + "," + live + ")"].join(
      ",",
    ) +
    ")"
  let frame = "tlsf_page_publish_frame(" +
    [p, cap, s, live, b, "(i : Num)"].join(",") +
    ")"
  let shared = [
    frame,
    "tlsf_small_links(" + bs + ")",
    "tlsf_bytes(val(" + b + ")+12," + s + "-4)",
  ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let common = seq([
    gen,
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    g => {
      let eqs = g.0
        .to_array()
        .filter(t => {
          let c = @kernel.concl(t.1)
          @basics.is_eq(c) && @equal.lhs(c) is Var("live", _)
        })
        .map(t => t.1)
      let copies = g.0.to_array().map(t => @simp.rewrite_rule(ths(eqs))(t.1))
      seq(copies.map(th => @tactics.assume_tac(th)))(g)
    },
    publish_geometry("(lim : Num)", p, cap, s, b, bs, live, "(i : Num)"),
    g => {
      @tactics.assume_tac(
        block_under(
          malloc_publication_inst(thm("tlsf_page_publish_fast_address"), [d, s]),
          g,
        ),
      )(g)
    },
    g => {
      @tactics.assume_tac(
        block_under(
          malloc_publication_inst(thm("tlsf_page_publish_partial_address"), [
            d, s,
          ]),
          g,
        ),
      )(g)
    },
  ])
  let basevs = [
    ("d", w),
    ("lim", "Num"),
    ("p", w),
    ("cap", "Num"),
    ("s", "Num"),
    ("b", w),
    ("bs", lw),
    ("live", lw),
    ("i", "Num"),
    ("used0", w),
    ("prev0", w),
    ("l1", "Value"),
    ("l3", "Value"),
    ("l4", "Value"),
    ("fp", rty),
  ]
  let bytesEq = red(
    malloc_publication_inst(thm("tlsf_bytes_split"), [
      "val(" + p + ")+24",
      "4",
      "4",
    ]),
  )
  let byteRws = [
    bytesEq,
    thm("tlsf_bytes_word"),
    arith("∀ a : Num, (a+24)+4 == a+28"),
  ]
  let pagePost = malloc_publication_inst(
    thm("tlsf_page_publish_page_post"),
    args,
  )
  let bundle = "star(" +
    newer +
    ",star(tlsf_small_links(" +
    bs +
    "),tlsf_page_publish_payload(" +
    b +
    "," +
    s +
    ")))"
  let postbody = own([bundle, cell(ft, "tlsf_small_head(" + bs + ")")])
  let fresh = malloc_publication_inst(
    thm("tlsf_malloc_retry_publish_fresh_raw"),
    [
      d,
      p,
      b,
      "(word(" + s + ") : " + w + ")",
      "(word(" + total + ") : " + w + ")",
      "(used0 : " + w + ")",
      "tlsf_small_head(" + bs + ")",
      zero,
      "(l1 : Value)",
      "(l3 : Value)",
      "(l4 : Value)",
      own(shared + [pc(24, "prev0"), pc(28, "word(0)")]),
    ],
  )
  let freshLive = "(NIL : " + lw + ")"
  let freshCond = cond +
    " && live == " +
    freshLive +
    " && REVERSE(tlsf_small_slots(p,s," +
    total +
    ")) == CONS(b,bs)"
  let built = "tlsf_page_allocate_build(" +
    [p, cap, s, total, "(used0 : " + w + ")", "(prev0 : " + w + ")"].join(",") +
    ")"
  let _ = lemma(
    "tlsf_malloc_retry_publish_fresh_page",
    malloc_publication_quantify(basevs) +
    freshCond +
    " → sl_triple(st(NIL,[" +
    i32(p) +
    "," +
    i32(b) +
    "," +
    i32("word(" + s + ")") +
    "," +
    i32(p20) +
    ",l4,(original : Value)]," +
    own([built, cell(ft, "word(0)")]) +
    "),tlsf_malloc_retry_fresh(d,initialize_idx,page_idx,take_idx,ensure_idx),st([" +
    i32(pb) +
    "],[" +
    i32(p) +
    "," +
    i32(pb) +
    "," +
    i32("word(" + s + ")") +
    "," +
    i32(p20) +
    "," +
    i32("tlsf_small_head(" + bs + ")") +
    ",(original : Value)]," +
    postbody +
    "))",
    () => {
      seq([
        common,
        g => {
          let pre = block_under(
            malloc_publication_inst(thm("tlsf_page_publish_fresh_view"), [
              "(lim : Num)",
              p,
              cap,
              s,
              b,
              bs,
              "(i : Num)",
              "(used0 : " + w + ")",
              "(prev0 : " + w + ")",
            ]),
            g,
          )
          let post = block_under(pagePost, g)
          by_path(
            fresh,
            "T",
            [pre],
            ["(prev0 : " + w + ")", zero],
            [post] + byteRws,
            [],
          )(g)
        },
      ])
    },
  )
  for hasNext in [false, true] {
    let np = if hasNext { "(nextp : " + w + ")" } else { zero }
    let zs = if hasNext {
      "CONS(" + np + ",(zs : " + lw + "))"
    } else {
      "(NIL : " + lw + ")"
    }
    let oldPart = "tlsf_small_partial_links(word(0),CONS(" + p + "," + zs + "))"
    let newPart = "tlsf_small_partial_links(word(0)," + zs + ")"
    let partRest = if hasNext {
      [
        cell("val(" + np + ")+28", "tlsf_small_head((zs : " + lw + "))"),
        "tlsf_small_partial_links(" + np + ",(zs : " + lw + "))",
      ]
    } else {
      []
    }
    let raw = malloc_publication_inst(
      thm(
        "tlsf_malloc_retry_publish_partial_" +
        (if hasNext { "cons" } else { "nil" }) +
        "_raw",
      ),
      [
        d,
        p,
        b,
        "(word(" + s + ") : " + w + ")",
        "(word(" + total + ") : " + w + ")",
        "(word(tlsf_small_used((NIL : " + lw + ")," + live + ")) : " + w + ")",
        "tlsf_small_head(" + bs + ")",
        zero,
        "(l1 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
        own(shared + [pc(24, "word(0)")] + partRest),
        np,
      ],
    )
    let q = own([
      bundle,
      cell(ft, "tlsf_small_head(" + bs + ")"),
      cell(pt, "tlsf_small_head(" + zs + ")"),
      newPart,
    ])
    let _ = lemma(
      "tlsf_malloc_retry_publish_partial_" +
      (if hasNext { "cons" } else { "nil" }) +
      "_page",
      malloc_publication_quantify(basevs + [("nextp", w), ("zs", lw)]) +
      cond +
      (if hasNext {
        " && !(nextp == word(0)) && val(nextp)+32 <= 4294967296"
      } else {
        ""
      }) +
      " → sl_triple(st(NIL,[" +
      i32(p) +
      ",l1," +
      i32("word(" + s + ")") +
      ",l3,l4,(original : Value)]," +
      own([old, cell(ft, "word(0)"), cell(pt, p), oldPart]) +
      "),tlsf_malloc_retry_partial(d,initialize_idx,page_idx,take_idx,ensure_idx),st([" +
      i32(pb) +
      "],[" +
      i32(np) +
      "," +
      i32(b) +
      "," +
      i32("word(" + s + ")") +
      "," +
      i32(p20) +
      "," +
      i32("tlsf_small_head(" + bs + ")") +
      ",(original : Value)]," +
      q +
      "))",
      () => {
        seq([
          common,
          if hasNext {
            free_have(
              "val(word_add(" +
              np +
              ",(word(24) : " +
              w +
              "))) == val(" +
              np +
              ")+24",
              seq([
                @logic.match_mp_tac(thm("val_add_small")),
                @int.asm_arith_tac,
              ]),
            )
          } else {
            @tactics.all_tac
          },
          g => {
            let pre = block_under(
              malloc_publication_inst(thm("tlsf_page_publish_page_pre"), args),
              g,
            )
            let post = block_under(pagePost, g)
            by_path(
              raw,
              "T",
              [
                pre,
                thm("tlsf_small_partial_links"),
                thm("tlsf_small_head"),
                @lists.not_cons_nil(),
                @lists.hd(),
              ],
              [zero, "tlsf_small_head(" + zs + ")"],
              [
                post,
                thm("tlsf_small_partial_links"),
                thm("tlsf_small_head"),
                @lists.not_cons_nil(),
                @lists.hd(),
              ] +
              byteRws,
              [],
            )(g)
          },
        ])
      },
    )
  }
}
