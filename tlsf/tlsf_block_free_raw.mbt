// Local store triples retain the caller's entire frame. In particular the
// old contents of the returned client payload are arbitrary, not zero.

///|
fn prove_tlsf_block_free_raw() -> Unit raise {
  let w = w32
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let at = (p : String, n : Int32) => "word_add((\{p} : \{w}),word(\{n}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star(ps+["(fp : "+rty+")(gs,ms)"])}"
  }
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
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ b : \{w}, ∀ p : \{w}, ∀ u : \{w}, ∀ head : \{w}, ∀ old : \{w}, ∀ l0 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let before = [
    cell(at("b", 4), "p"),
    cell(at("b", 8), "old"),
    cell(at("p", 20), "head"),
    cell(at("p", 16), "u"),
  ]
  let after = [
    cell(at("b", 4), "p"),
    cell(at("b", 8), "head"),
    cell(at("p", 20), "b"),
    cell(at("p", 16), "word_sub((u : " + w + "),word(1))"),
  ]
  ignore(
    sym_prove(
      "tlsf_block_free_release_raw",
      "\{vars}, sl_triple(st(NIL,[l0,\{i("b")},l2],\{own(before)}),tlsf_block_free_release(d,free_idx),st(NIL,[\{i("p")},\{i("u")},l2],\{own(after)}))",
      [],
      [vc],
      kind="lemma",
    ),
  )
  let p = "(p : \{w})"
  let size = "(size : \{w})"
  let cls = "word_jushr(word_add(\{size},word(7)),word(3))"
  let table = "word_add(word_add(word_and(word_add((d : \{w}),word(15)),word(4294967280)),word_jshl(\{cls},word(3))),word(1916))"
  let env = "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ size : \{w}, ∀ nx : \{w}, ∀ prev0 : \{w}, ∀ next0 : \{w}, ∀ nxprev : \{w}, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  for nonempty in [false, true] {
    let nx = if nonempty { "(nx : " + w + ")" } else { "(word(0) : " + w + ")" }
    let cond = if nonempty {
      "!(nx == word(0)) && !(p == word(0))"
    } else {
      "!(p == word(0))"
    }
    let before = [
        cell(at(p, 8), size),
        cell(at(p, 24), "prev0"),
        cell(at(p, 28), "next0"),
        cell(table, nx),
      ] +
      (if nonempty { [cell(at(nx, 24), "nxprev")] } else { [] })
    let after = [
        cell(at(p, 8), size),
        cell(at(p, 24), "word(0)"),
        cell(at(p, 28), nx),
        cell(table, p),
      ] +
      (if nonempty { [cell(at(nx, 24), p)] } else { [] })
    // The first if updates nx.prev; the second checks p, which the invariant
    // proves non-null. Neither has a fall-through effect on the stack.
    let mid = [
        cell(at(p, 8), size),
        cell(at(p, 24), "prev0"),
        cell(at(p, 28), nx),
        cell(table, nx),
      ] +
      (if nonempty { [cell(at(nx, 24), p)] } else { [] })
    let after1 = "st(NIL,[\{i(p)},\{i(nx)},\{i(cls)}],\{own(mid)})"
    let after2 = "st(NIL,[\{i(p)},\{i(nx)},\{i(cls)}],\{own(after)})"
    ignore(
      sym_prove(
        "tlsf_block_free_publish_\{if nonempty { "cons" } else { "nil" }}_raw",
        "\{env}, \{cond} → sl_triple(st(NIL,[\{i(p)},u,l2],\{own(before)}),tlsf_block_free_publish(d,free_idx),st([\{i("word(0)")}],[\{i(p)},\{i(nx)},\{i(cls)}],\{own(after)}))",
        [],
        [vc, vc],
        afters=[after1, after2],
        kind="lemma",
      ),
    )
  }
  for has_prev in [false, true] {
    for has_next in [false, true] {
      let nx = if has_next {
        "(nx : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let pr = "(pr : " + w + ")"
      let prevcells = if has_prev {
        [cell(at(pr, 28), p)]
      } else {
        [cell(at(p, 8), size), cell(table, p)]
      }
      let afterprev = if has_prev {
        [cell(at(pr, 28), nx)]
      } else {
        [cell(at(p, 8), size), cell(table, nx)]
      }
      let before = [
          cell(at(p, 24), if has_prev { pr } else { "word(0)" }),
          cell(at(p, 28), nx),
        ] +
        prevcells +
        (if has_next { [cell(at(nx, 24), p)] } else { [] })
      let after = [
          cell(at(p, 24), if has_prev { pr } else { "word(0)" }),
          cell(at(p, 28), nx),
        ] +
        afterprev +
        (if has_next {
          [cell(at(nx, 24), if has_prev { pr } else { "word(0)" })]
        } else {
          []
        })
      let name = "tlsf_block_free_unlink_" +
        (if has_prev { "prev" } else { "head" }) +
        "_" +
        (if has_next { "cons" } else { "nil" }) +
        "_raw"
      let condition = (if has_prev { "!(pr == word(0))" } else { "T" }) +
        (if has_next { " && !(nx == word(0))" } else { "" })
      let new2 = if has_prev { pr } else { cls }
      let branch = if has_prev {
        "tlsf_block_free_unlink_prev"
      } else {
        "tlsf_block_free_unlink_head"
      }
      let new1 = nx
      let out = "st([" +
        i("word(0)") +
        "],[" +
        i(p) +
        "," +
        i(new1) +
        "," +
        i(new2) +
        "]," +
        own(after) +
        ")"
      let mid = "st(NIL,[" +
        i(p) +
        "," +
        i(new1) +
        "," +
        i(new2) +
        "]," +
        own(after) +
        ")"
      ignore(
        sym_prove(
          name,
          "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ pr : \{w}, ∀ nx : \{w}, ∀ size : \{w}, ∀ l2 : Value, ∀ fp : \{rty}, " +
          condition +
          " → sl_triple(st(NIL,[" +
          i(p) +
          "," +
          (if has_prev { i(at(p, 24)) } else { i("word(0)") }) +
          ",l2]," +
          own(before) +
          ")," +
          branch +
          "(d,free_idx)," +
          out +
          ")",
          [],
          [vc],
          afters=[mid],
          kind="lemma",
        ),
      )
    }
  }
}
