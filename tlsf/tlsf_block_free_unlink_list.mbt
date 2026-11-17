// Lift the full compiled unlink prefix to a split partial-page list. Interior
// prefix/suffix links and the client frame are carried through unchanged.

///|
fn prove_tlsf_block_free_unlink_list() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let head_append = lemma(
    "tlsf_small_head_append",
    "∀ a : \{lw}, ∀ z : \{lw}, !(a == NIL) → tlsf_small_head(APPEND(a,z)) == tlsf_small_head(a)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          @lists.append(),
          @lists.not_cons_nil(),
          thm("tlsf_small_head"),
          @lists.hd(),
        ]),
      ])
    },
  )
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (p : String, k : Int32, v : String) => {
    "pts(val((\{p} : \{w}))+\{k},serialise_i32((\{v} : \{w})))"
  }
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ s : Num, ∀ a : \{lw}, ∀ nx : \{w}, ∀ tail : \{lw}, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let cls = "DIV((s : Num),8)"
  let table = "val(tlsf_base((d : \{w})))+1916+8*\{cls}"
  let hword = (v : String) => "pts(\{table},serialise_i32((\{v} : \{w})))"
  for has_prev in [false, true] {
    for has_next in [false, true] {
      let a = if has_prev { "(a : " + lw + ")" } else { "(NIL : " + lw + ")" }
      let z = if has_next {
        "CONS((nx : " + w + "),(tail : " + lw + "))"
      } else {
        "(NIL : " + lw + ")"
      }
      let pr = if has_prev {
        "tlsf_small_last((word(0) : " + w + ")," + a + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let nx = if has_next {
        "(nx : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let old = "APPEND(" + a + ",CONS((p : " + w + ")," + z + "))"
      let newer = "APPEND(" + a + "," + z + ")"
      let pre = own([
        cell("p", 8, "word(s)"),
        hword("tlsf_small_head(" + old + ")"),
        "tlsf_small_partial_links((word(0) : " + w + ")," + old + ")",
      ])
      let post = own([
        cell("p", 8, "word(s)"),
        hword("tlsf_small_head(" + newer + ")"),
        "tlsf_small_partial_links((word(0) : " + w + ")," + newer + ")",
        cell("p", 24, pr),
        cell("p", 28, nx),
      ])
      let frame = own(
        [
          "tlsf_small_dtail((word(0) : " + w + ")," + a + ")",
          "tlsf_small_dhead(" + z + ",(word(0) : " + w + "))",
        ] +
        (if has_prev {
          [cell("p", 8, "word(s)"), hword("tlsf_small_head(" + old + ")")]
        } else {
          []
        }),
      )
      let cond = "val((d : \{w})) <= 4294965088 && 8 <= (s : Num) && s <= 256 && MOD(s,8) == 0 && val((p : \{w}))+32 <= 4294967296" +
        (if has_prev {
          " && !((a : " +
          lw +
          ") == NIL) && !((" +
          pr +
          ") == word(0)) && val(" +
          pr +
          ")+32 <= 4294967296"
        } else {
          ""
        }) +
        (if has_next {
          " && !((nx : " + w + ") == word(0)) && val(nx)+32 <= 4294967296"
        } else {
          ""
        })
      let name = "tlsf_block_free_unlink_" +
        (if has_prev { "prev" } else { "head" }) +
        "_" +
        (if has_next { "cons" } else { "nil" }) +
        "_list"
      let _ = lemma(
        name,
        "\{vars}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_unlink(d,free_idx),st(NIL,[\{i("p")},\{i(nx)},\{i(if has_prev { pr } else { "word("+cls+")" })}],\{post}))",
        () => {
          seq([
            gen,
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_small_table_address"), [
                    "(d : " + w + ")",
                    "(s : Num)",
                  ]),
                  g,
                ),
              )(g)
            },
            seq(
              ([
                ("(p : " + w + ")", 8),
                ("(p : " + w + ")", 24),
                ("(p : " + w + ")", 28),
              ] +
              (if has_prev { [(pr, 28)] } else { [] }) +
              (if has_next { [(nx, 24)] } else { [] })).map(v => {
                free_have(
                  "val(word_add((\{v.0} : \{w}),word(\{v.1}))) == val(\{v.0})+\{v.1}",
                  seq([
                    @tactics.match_mp_tac(thm("val_add_small")),
                    @int.asm_arith_tac,
                  ]),
                )
              }),
            ),
            g => {
              let path = inst(
                thm(
                  "tlsf_block_free_unlink_" +
                  (if has_prev { "prev" } else { "head" }) +
                  "_" +
                  (if has_next { "cons" } else { "nil" }) +
                  "_all_raw",
                ),
                [
                  "(d : " + w + ")",
                  "(free_idx : Num)",
                  "(p : " + w + ")",
                  pr,
                  nx,
                  "(word((s : Num)) : " + w + ")",
                  "(u : Value)",
                  "(l2 : Value)",
                  frame,
                ],
              )
              let classTh = @kernel.assume_rule(
                tm(
                  "word_jushr(word_add((word((s : Num)) : " +
                  w +
                  "),word(7)),word(3)) == word(DIV(s,8))",
                ),
              )
              let scalar = ths([thm("tlsf_base"), classTh])
              let math = g.0
                .to_array()
                .map(v => @simp.rewrite_rule(scalar)(v.1)) +
                [
                  classTh,
                  thm("tlsf_base"),
                  thm("tlsf_small_partial_dlist"),
                  @lists.append(),
                  thm("tlsf_small_dtail"),
                  thm("tlsf_small_dhead"),
                  thm("tlsf_small_first"),
                  thm("tlsf_small_last_nil"),
                  thm("tlsf_small_dlist_nil"),
                  thm("tlsf_small_head"),
                  @lists.not_cons_nil(),
                  @lists.hd(),
                  @arith.add_clauses(),
                ]
              let headrw = if has_prev {
                [
                  block_under(
                    inst(head_append, [a, "CONS((p : " + w + ")," + z + ")"]),
                    g,
                  ),
                  block_under(inst(head_append, [a, z]), g),
                ]
              } else {
                []
              }
              let listnorm = ths([
                @lists.append(),
                thm("tlsf_small_first"),
                thm("tlsf_small_last_nil"),
                thm("tlsf_small_dtail"),
                thm("tlsf_small_dhead"),
                thm("tlsf_small_dlist_nil"),
                @lists.not_cons_nil(),
                @lists.hd(),
                thm("star_emp_hl"),
                thm("star_emp_hr"),
              ])
              let before = @simp.rewrite_rule(listnorm)(
                inst(thm("tlsf_small_dlist_unlink_view"), [
                  a,
                  z,
                  "(word(0) : " + w + ")",
                  "(word(0) : " + w + ")",
                  "(p : " + w + ")",
                ]),
              )
              let after = @simp.rewrite_rule(listnorm)(
                inst(thm("tlsf_small_dlist_removed_view"), [
                  a,
                  z,
                  "(word(0) : " + w + ")",
                  "(word(0) : " + w + ")",
                ]),
              )
              by_path(
                path,
                "T",
                [before] + headrw + math,
                [],
                [after] + headrw + math,
                [],
              )(g)
            },
          ])
        },
      )
    }
  }
}
