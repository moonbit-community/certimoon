// Focus the selected page and size-class cache, preserving all other cells.

///|
fn prove_tlsf_malloc_cached_small() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let s = "8*" + k
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let n = malloc_cached_args(a, p, b, bs, k)
  let vs = malloc_publication_variables() +
    page_model_variables() +
    [
      ("p", w),
      ("b", w),
      ("bs", lw),
      ("k", "Num"),
      ("i", "Num"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
      ("fp", rty),
    ]
  let page = "tlsf_small_page_ok(" +
    [
      a[1],
      p,
      cap,
      s,
      a[10] + "(" + p + ")",
      a[11] + "(" + p + ")",
      a[12] + "(" + p + ")",
    ].join(",") +
    ")"
  let own = (xs : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(xs + ["(fp : " + rty + ")(gs,ms)"])
  }
  let pre = own([block_pages(a), block_table(a)])
  let post = own([
    block_pages(n),
    block_table(n),
    "tlsf_page_publish_payload(" + b + "," + s + ")",
  ])
  let pb = "word_add(" + b + ",word(8))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let cond = "val(" +
    a[0] +
    ") <= 4294965088 && " +
    page +
    " && MEM(" +
    b +
    "," +
    a[11] +
    "(" +
    p +
    ")) && (i : Num) < tlsf_small_total(" +
    s +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    s +
    ",i) && tlsf_count(" +
    p +
    "," +
    a[8] +
    ") == 1 && " +
    a[9] +
    "(" +
    p +
    ") == " +
    s +
    " && " +
    k +
    " < 33 && " +
    a[13] +
    "(" +
    k +
    ") == CONS(" +
    b +
    "," +
    bs +
    ")"
  for v in malloc_variant_names() {
    let _ = lemma(
      "tlsf_malloc_" + v + "_cached_small",
      page_quantify(vs) +
      cond +
      " → sl_triple(st(NIL," +
      malloc_locals(v, [
        malloc_i(b),
        malloc_i("word(" + k + ")"),
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      ]) +
      "," +
      pre +
      ")," +
      malloc_part(v, "cached") +
      ",(res : List[Value]) => (lc2 : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => lc2 == " +
      malloc_suffix_locals(v, "cached") +
      " && res == [" +
      malloc_i(pb) +
      "] && (" +
      post +
      ")(gs,ms,h))",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          free_have(
            "8 <= " + s + " && " + s + " <= 256 && MOD(" + s + ",8) == 0",
            seq([
              @tactics.undisch_tac(tm(page)),
              @simp.rewrite_tac(ths([thm("tlsf_small_page_ok")])),
              page_publish_atomic([]),
            ]),
          ),
          split_conjs(),
          g => {
            @tactics.strip_assume_tac(
              block_under(
                inst(thm("tlsf_small_slot_bounds"), [
                  a[1],
                  p,
                  cap,
                  s,
                  a[10] + "(" + p + ")",
                  a[11] + "(" + p + ")",
                  a[12] + "(" + p + ")",
                  "(i : Num)",
                ]),
                g,
              ),
            )(g)
          },
          free_have(
            "val(word_add(" + b + ",word(8))) == val(" + b + ")+8",
            seq([
              @logic.match_mp_tac(thm("val_add_small")),
              free_have(
                "(lim : Num) <= 4294967296 && val(" +
                p +
                ")+8+" +
                cap +
                " <= (lim : Num)",
                seq([
                  @tactics.undisch_tac(tm(page)),
                  @simp.rewrite_tac(ths([thm("tlsf_small_page_ok")])),
                  page_publish_atomic([]),
                ]),
              ),
              split_conjs(),
              arw([]),
              @int.asm_arith_tac,
            ]),
          ),
          g => {
            let focusOld = block_under(
              inst(thm("tlsf_small_table_focus"), [a[0], a[13], a[14], k]),
              g,
            )
            let rest = args_of(@equal.rhs(@kernel.concl(focusOld)), "star", 2).unwrap()[1]
            let focusNew0 = block_under(
              inst(thm("tlsf_small_table_focus"), [a[0], n[13], n[14], k]),
              g,
            )
            let restEq = @simp.rewrite_rule(
              ths([thm("tlsf_page_publish_put_class_same")]),
            )(
              inst(
                thm("tlsf_page_publish_table_rest"),
                a + [p, b, bs, s, k, a[14] + "(" + k + ")"],
              ),
            )
            let focusNew = @equal.conv_rule(
              @equal.rand_conv(@equal.subs_conv(ths([restEq]))),
              focusNew0,
            )
            let pageOld = block_under(
              inst(thm("tlsf_small_pages_focus"), [
                a[8],
                a[4],
                a[9],
                a[10],
                a[11],
                a[12],
                p,
              ]),
              g,
            )
            let pageNew = block_under(
              inst(thm("tlsf_small_pages_focus"), [
                n[8],
                n[4],
                n[9],
                n[10],
                n[11],
                n[12],
                p,
              ]),
              g,
            )
            let pageView = block_under(
              inst(thm("tlsf_malloc_cache_page_view"), [
                a[1],
                p,
                cap,
                s,
                a[10] + "(" + p + ")",
                a[11] + "(" + p + ")",
                a[12] + "(" + p + ")",
                b,
                "(i : Num)",
              ]),
              g,
            )
            let r = a.copy()
            r[8] = "tlsf_small_remove(" + p + "," + a[8] + ")"
            let frame = own([
              "tlsf_small_page_heap(" +
              [
                p,
                cap,
                s,
                a[10] + "(" + p + ")",
                n[11] + "(" + p + ")",
                n[12] + "(" + p + ")",
              ].join(",") +
              ")",
              block_pages(r),
              show(rest),
              "tlsf_bytes(val(" + b + ")+12," + s + "-4)",
              "pts(val(tlsf_base(" +
              a[0] +
              "))+1916+8*" +
              k +
              ",serialise_i32(tlsf_small_head(" +
              a[14] +
              "(" +
              k +
              "))))",
              "tlsf_small_partial_links(word(0)," + a[14] + "(" + k + "))",
              "tlsf_small_links(" + bs + ")",
            ])
            let path = inst(
              thm("tlsf_malloc_" + v + "_cached_raw"),
              malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")") +
              [
                b,
                "(word(" + k + ") : " + w + ")",
                "tlsf_small_head(" + bs + ")",
                "(l2 : Value)",
                "(l3 : Value)",
                "(l4 : Value)",
                "(original : Value)",
                frame,
              ],
            )
            let ft = block_under(
              inst(thm("tlsf_page_publish_fast_address"), [a[0], s]),
              g,
            )
            let shift = block_under(
              inst(thm("tlsf_malloc_small_shift"), [k]),
              g,
            )
            let comm = @words.word_rule(
              tm(
                "word_add(word_add(tlsf_base(" +
                a[0] +
                "),word(1912)),(word(" +
                s +
                ") : " +
                w +
                ")) == word_add(word(" +
                s +
                "),word_add(tlsf_base(" +
                a[0] +
                "),word(1912)))",
              ),
            )
            let comm = @simp.rewrite_rule(ths([thm("tlsf_base")]))(comm)
            let defs = [
              comm,
              thm("tlsf_small_table_item"),
              thm("tlsf_small_head"),
              thm("tlsf_small_links"),
              thm("tlsf_small_put"),
              thm("tlsf_small_put_class"),
              thm("tlsf_base"),
              @lists.hd(),
              @lists.tl(),
              @lists.not_cons_nil(),
              shift,
              ft,
            ]
            let prest = [focusOld, pageOld, pageView] + defs
            let postst = [
                focusNew,
                pageNew,
                inst(thm("tlsf_malloc_cached_pages_rest"), a + [p, b, bs, k]),
                thm("tlsf_page_publish_payload"),
              ] +
              defs
            by_path(path, "T", prest, [], postst, [])(g)
          },
        ])
      },
    )
  }
}
