// The compiler's two merge-store sequences. All other cells and bytes
// remain in fp, including the payloads of other live allocations.

///|
fn prove_tlsf_free_writes() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (ps : Array[String]) => {
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    "(gs : List[Value]) => (ms : Num) => \{out}"
  }
  let vc = seq([
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.asm_rewrite_tac(
      ths([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
    ),
  ])
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ r : \{w}, ∀ hm : \{w}, ∀ hr : \{w}, ∀ top : \{w}, ∀ l2 : Value, ∀ fp : \{rty}"
  let merged = "word_or(word_and((hm : \{w}),word(3)),word_add(word_add(word_and(hm,word(4294967292)),word_and((hr : \{w}),word(4294967292))),word(8)))"
  let endprev = "word_add(word_add((r : \{w}),word_and((hr : \{w}),word(4294967292))),word(12))"
  for prev in [true, false] {
    // m is the left block, r the right block, in either instruction order.
    let lc = if prev {
      "[\{i("r")},\{i("m")},(l2 : Value)]"
    } else {
      "[\{i("m")},\{i("r")},(l2 : Value)]"
    }
    let midlc = if prev {
      "[\{i("r")},\{i("m")},\{i("hm")}]"
    } else {
      "[\{i("m")},\{i("r")},\{i("hm")}]"
    }
    let outlc = if prev { "[\{i("m")},\{i("m")},\{i("hm")}]" } else { midlc }
    for last in [true, false] {
      let ph = [cell("m", "hm"), cell("r", "hr")]
      let qh = [
        cell(
          "m",
          if last {
            "word_or(word_and(\{merged},word(4294967293)),word(2))"
          } else {
            merged
          },
        ),
        cell("r", "hr"),
      ]
      if last {
        ph.push(cell("tlsf_top_cell((d : " + w + "))", "top"))
        qh.push(cell("tlsf_top_cell((d : " + w + "))", "m"))
      } else {
        ph.push(cell(endprev, "r"))
        qh.push(cell(endprev, "m"))
      }
      let p = pred(ph)
      let q = pred(qh)
      let cond = if last {
        "!(word_and((hr : \{w}),word(2)) == word(0))"
      } else {
        "word_and((hr : \{w}),word(2)) == word(0)"
      }
      let _ = sym_prove(
        "tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        (if last { "_last_write_raw" } else { "_next_write_raw" }),
        "\{vars}, \{cond} → sl_triple(st(NIL,\{lc},\{p}),tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        "_write(d,pop,push),st(NIL,\{outlc},\{q}))",
        [],
        [vc],
        afters=if prev { ["st(NIL,\{midlc},\{q})"] } else { [] },
        rws=[thm("tlsf_top_cell"), thm("tlsf_base")],
      )
    }
  }
}
