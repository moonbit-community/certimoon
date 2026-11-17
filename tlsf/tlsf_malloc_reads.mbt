// Persistent read views for the dispatch tables keep the saved heap exact.

///|
fn prove_tlsf_malloc_reads() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let client = "(client : " + hprop + ")"
  let h = "(h : " + heap + ")"
  let own = "star(tlsf_allocator(" + a.join(",") + ")," + client + "," + h + ")"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let _ = lemma(
    "tlsf_malloc_allocator_facts",
    page_quantify(model + [("client", hprop), ("h", heap)]) +
    own +
    " → " +
    physical +
    " && " +
    block_backing(a) +
    " && " +
    block_lists(a),
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_allocator"),
          thm("tlsf_small"),
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("star"),
        ]),
        strip,
        small_meson(ths([])),
      ])
    },
  )
  let slot = "word_add(tlsf_base(" + a[0] + "),word(1908))"
  let _ = lemma(
    "tlsf_malloc_read_top",
    page_quantify(model + [("client", hprop), ("h", heap)]) +
    own +
    " → has_i32(" +
    h +
    ",val(" +
    slot +
    ")," +
    a[2] +
    ")",
    () => {
      ent_tac(
        [
          thm("tlsf_allocator"),
          thm("tlsf_small"),
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("has_i32"),
        ],
        [
          small_star([
            "tlsf_regions(word(0)," + a[3] + "," + a[4] + ")",
            "tlsf_bins(" + [a[0], a[5], a[6], a[7]].join(",") + ")",
            block_pages(a),
            block_table(a),
            client,
          ]),
        ],
      )
    },
  )
  for fast in [true, false] {
    let k = "(k : Num)"
    let read = "tlsf_small_head(" +
      a[if fast { 13 } else { 14 }] +
      "(" +
      k +
      "))"
    let addr = "val(tlsf_base(" +
      a[0] +
      "))+" +
      (if fast { "1912" } else { "1916" }) +
      "+8*" +
      k
    let _ = lemma(
      "tlsf_malloc_read_" + (if fast { "fast" } else { "partial" }),
      page_quantify(model + [("k", "Num"), ("client", hprop), ("h", heap)]) +
      k +
      " < 33 → (" +
      own +
      " → has_i32(" +
      h +
      "," +
      addr +
      "," +
      read +
      "))",
      () => {
        seq([
          gen,
          @tactics.disch_tac,
          g => {
            let focus = block_under(
              inst(thm("tlsf_small_table_focus"), [a[0], a[13], a[14], k]),
              g,
            )
            let rest = show(
              args_of(@equal.rhs(@kernel.concl(focus)), "star", 2).unwrap()[1],
            )
            let fr = small_star([
              block_large(a),
              block_pages(a),
              rest,
              client,
              "tlsf_small_links(" + a[13] + "(" + k + "))",
              "tlsf_small_partial_links(word(0)," + a[14] + "(" + k + "))",
              "pts(val(tlsf_base(" +
              a[0] +
              "))+" +
              (if fast { "1916" } else { "1912" }) +
              "+8*" +
              k +
              ",serialise_i32(tlsf_small_head(" +
              a[if fast { 14 } else { 13 }] +
              "(" +
              k +
              "))))",
            ])
            ent_tac(
              [
                thm("tlsf_allocator"),
                thm("tlsf_small"),
                focus,
                thm("tlsf_small_table_item"),
                thm("has_i32"),
              ],
              [fr],
            )(g)
          },
        ])
      },
    )
  }
  let _ = lemma(
    "tlsf_malloc_initialized_guards",
    page_quantify(model) +
    physical +
    " → val(" +
    a[0] +
    ") <= 4294965088 && !word_uge(word_jushr(" +
    slot +
    ",word(16)),(word(DIV(" +
    a[1] +
    ",65536)) : " +
    w +
    ")) && !(" +
    a[2] +
    " == word(0))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_physical_last"), a[:5].to_owned()), g),
          )(g)
        },
        subst_only("xs"),
        g => {
          @tactics.strip_assume_tac(
            @simp.rewrite_rule(ths([thm("tlsf_top_cell")]))(
              block_under(
                inst(thm("tlsf_ensure_metadata_guards"), [
                  "(ys : List[" + w + "])",
                  a[0],
                  a[1],
                  a[2],
                  a[4],
                ]),
                g,
              ),
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(thm("tlsf_ensure_top_facts"), [
                "(ys : List[" + w + "])",
                a[0],
                a[1],
                a[2],
                a[4],
              ]),
              g,
            ),
          )(g)
        },
        free_have(
          "val(" + a[0] + ") <= 4294965088",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_physical_ok(" +
                [
                  a[0],
                  a[1],
                  a[2],
                  "APPEND((ys : List[" + w + "]),[" + a[2] + "])",
                  a[4],
                ].join(",") +
                ")",
              ),
            ),
            rw([thm("tlsf_physical_ok")]),
            page_publish_atomic([]),
          ]),
        ),
        arw([]),
        rw([@equal.gsym(@words.val_eq_0())]),
        @int.asm_arith_tac,
      ])
    },
  )
}
