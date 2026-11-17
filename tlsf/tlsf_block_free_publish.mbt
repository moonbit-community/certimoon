// Lift the compiled publish fragment from head/back-link cells to an entire
// partial-page list. The old unpublished link words may contain any bytes.

///|
fn prove_tlsf_block_free_publish() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (p : String, k : Int32, v : String) => {
    "pts(val((\{p} : \{w}))+\{k},serialise_i32((\{v} : \{w})))"
  }
  let cls = "DIV((s : Num),8)"
  let table = "val(tlsf_base((d : \{w})))+1916+8*\{cls}"
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ s : Num, ∀ nx : \{w}, ∀ tail : \{lw}, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  for nonempty in [false, true] {
    let list = if nonempty {
      "CONS((nx : " + w + "),(tail : " + lw + "))"
    } else {
      "(NIL : " + lw + ")"
    }
    let head = if nonempty {
      "(nx : " + w + ")"
    } else {
      "(word(0) : " + w + ")"
    }
    let owner = (ps : Array[String]) => {
      "(gs : List[Value]) => (ms : Num) => " +
      small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
    }
    let hword = (v : String) => "pts(\{table},serialise_i32((\{v} : \{w})))"
    let pre = owner([
      cell("p", 8, "word(s)"),
      "tlsf_bytes(val((p : " + w + "))+24,8)",
      hword("tlsf_small_head(" + list + ")"),
      "tlsf_small_partial_links((word(0) : " + w + ")," + list + ")",
    ])
    let post = owner([
      cell("p", 8, "word(s)"),
      hword("p"),
      "tlsf_small_partial_links((word(0) : " +
      w +
      "),CONS((p : " +
      w +
      ")," +
      list +
      "))",
    ])
    let cond = "val((d : \{w})) <= 4294965088 && 8 <= (s : Num) && s <= 256 && MOD(s,8) == 0 && !((p : \{w}) == word(0)) && val(p)+32 <= 4294967296" +
      (if nonempty {
        " && !((nx : " + w + ") == word(0)) && val(nx)+32 <= 4294967296"
      } else {
        ""
      })
    let tailframe = if nonempty {
      "(gs : List[Value]) => (ms : Num) => " +
      small_star([
        cell("nx", 28, "tlsf_small_head((tail : " + lw + "))"),
        "tlsf_small_partial_links((nx : " + w + "),(tail : " + lw + "))",
        "(fp : " + rty + ")(gs,ms)",
      ])
    } else {
      "(fp : " + rty + ")"
    }
    let _ = lemma(
      "tlsf_block_free_publish_" +
      (if nonempty { "cons" } else { "nil" }) +
      "_list",
      "\{vars}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_publish(d,free_idx),st([\{i("word(0)")}],[\{i("p")},\{i(head)},\{i("word("+cls+")")}],\{post}))",
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
            ([("p", 8), ("p", 24), ("p", 28)] +
            (if nonempty { [("nx", 24)] } else { [] })).map(v => {
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
                "tlsf_block_free_publish_" +
                (if nonempty { "cons" } else { "nil" }) +
                "_raw",
              ),
              [
                "(d : " + w + ")",
                "(free_idx : Num)",
                "(p : " + w + ")",
                "(word((s : Num)) : " + w + ")",
                head,
                "(x : " + w + ")",
                "(y : " + w + ")",
                "(word(0) : " + w + ")",
                "(u : Value)",
                "(l2 : Value)",
                tailframe,
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
            let math = g.0.to_array().map(v => @simp.rewrite_rule(scalar)(v.1)) +
              [
                classTh,
                thm("tlsf_base"),
                thm("tlsf_small_partial_links"),
                thm("tlsf_small_head"),
                @lists.not_cons_nil(),
                @lists.hd(),
                @arith.add_clauses(),
                arith("∀ a : Num, a+24+4 == a+28"),
              ]
            by_path(
              path,
              if nonempty {
                "!((p : " +
                w +
                ") == word(0)) && !((nx : " +
                w +
                ") == word(0))"
              } else {
                "!((p : " + w + ") == word(0))"
              },
              math + [thm("tlsf_bytes_two_words")],
              [],
              math,
              ["(x : " + w + ")", "(y : " + w + ")"],
            )(g)
          },
        ])
      },
    )
  }
}
