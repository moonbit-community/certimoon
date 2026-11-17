// Remove a page from one class while framing the whole rest of the table.

///|
fn prove_tlsf_block_free_unlink_table() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let k = "DIV((s : Num),8)"
  let partial = "(partial : (Num) -> \{lw})"
  let fast = "(fast : (Num) -> \{lw})"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (p : String, n : Int32, v : String) => {
    "pts(val((\{p} : \{w}))+\{n},serialise_i32((\{v} : \{w})))"
  }
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}, ∀ s : Num, ∀ a : \{lw}, ∀ nx : \{w}, ∀ tail : \{lw}, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
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
      let entries = "APPEND(" + a + "," + z + ")"
      let newer = "tlsf_small_put_class(" +
        partial +
        "," +
        k +
        "," +
        entries +
        ")"
      let rest = "tlsf_istar((j : Num) => if j == \{k} { emp } else { tlsf_small_table_item((d : \{w}),\{fast},\{partial},j) },33)"
      let pre = own([
        cell("p", 8, "word(s)"),
        "tlsf_small_table((d : " + w + ")," + fast + "," + partial + ")",
      ])
      let post = own([
        cell("p", 8, "word(s)"),
        "tlsf_small_table((d : " + w + ")," + fast + "," + newer + ")",
        cell("p", 24, pr),
        cell("p", 28, nx),
      ])
      let frame = own([
        rest,
        "pts(val(tlsf_base((d : " +
        w +
        ")))+1912+8*" +
        k +
        ",serialise_i32(tlsf_small_head(" +
        fast +
        "(" +
        k +
        "))))",
        "tlsf_small_links(" + fast + "(" + k + "))",
      ])
      let eq = "\{partial}(\{k}) == \{old}"
      let cond = "val((d : \{w})) <= 4294965088 && 8 <= (s : Num) && s <= 256 && MOD(s,8) == 0 && val((p : \{w}))+32 <= 4294967296 && \{eq}" +
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
      let label = (if has_prev { "prev" } else { "head" }) +
        "_" +
        (if has_next { "cons" } else { "nil" })
      let _ = lemma(
        "tlsf_block_free_unlink_" + label + "_table",
        "\{vars}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_unlink(d,free_idx),st(NIL,[\{i("p")},\{i(nx)},\{i(if has_prev { pr } else { "word("+k+")" })}],\{post}))",
        () => {
          seq([
            gen,
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            g => {
              @tactics.strip_assume_tac(
                block_under(
                  inst(thm("tlsf_small_class_bounds"), ["(s : Num)"]),
                  g,
                ),
              )(g)
            },
            g => {
              let focusOld = block_under(
                inst(thm("tlsf_small_table_focus"), [
                  "(d : " + w + ")",
                  fast,
                  partial,
                  k,
                ]),
                g,
              )
              let focusNew = block_under(
                inst(thm("tlsf_small_table_focus"), [
                  "(d : " + w + ")",
                  fast,
                  newer,
                  k,
                ]),
                g,
              )
              let restNew = inst(thm("tlsf_small_table_update_rest"), [
                "(d : " + w + ")",
                fast,
                partial,
                k,
                entries,
              ])
              let path = inst(
                thm("tlsf_block_free_unlink_" + label + "_list"),
                [
                  "(d : " + w + ")",
                  "(free_idx : Num)",
                  "(p : " + w + ")",
                  "(s : Num)",
                  a,
                  nx,
                  "(tail : " + lw + ")",
                  "(u : Value)",
                  "(l2 : Value)",
                  frame,
                ],
              )
              let common = [
                thm("tlsf_small_table_item"),
                @kernel.assume_rule(tm(eq)),
              ]
              by_path(
                path,
                "T",
                [focusOld] + common,
                [],
                [focusNew, restNew, thm("tlsf_small_put_class")] + common,
                [],
              )(g)
            },
          ])
        },
      )
    }
  }
}
