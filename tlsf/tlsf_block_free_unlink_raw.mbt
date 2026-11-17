// Include the predecessor test and administrative drop around the four
// unlink paths, so the complete compiled prefix composes with Memory::free.

///|
fn prove_tlsf_block_free_unlink_raw() -> Unit raise {
  let w = w32
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let at = (p : String, n : Int32) => "word_add((\{p} : \{w}),word(\{n}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
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
  let cls = "word_jushr(word_add((size : \{w}),word(7)),word(3))"
  let table = "word_add(word_add(word_and(word_add((d : \{w}),word(15)),word(4294967280)),word_jshl(\{cls},word(3))),word(1916))"
  for has_prev in [false, true] {
    for has_next in [false, true] {
      let nx = if has_next {
        "(nx : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let pr = if has_prev {
        "(pr : " + w + ")"
      } else {
        "(word(0) : " + w + ")"
      }
      let pre = [cell(at("p", 24), pr), cell(at("p", 28), nx)] +
        (if has_prev {
          [cell(at(pr, 28), "p")]
        } else {
          [cell(at("p", 8), "size"), cell(table, "p")]
        }) +
        (if has_next { [cell(at(nx, 24), "p")] } else { [] })
      let post = [cell(at("p", 24), pr), cell(at("p", 28), nx)] +
        (if has_prev {
          [cell(at(pr, 28), nx)]
        } else {
          [cell(at("p", 8), "size"), cell(table, nx)]
        }) +
        (if has_next { [cell(at(nx, 24), pr)] } else { [] })
      let lc = "[" +
        i("p") +
        "," +
        i(nx) +
        "," +
        i(if has_prev { pr } else { cls }) +
        "]"
      let mid = "st(NIL," + lc + "," + own(post) + ")"
      let out0 = "st([" + i("word(0)") + "]," + lc + "," + own(post) + ")"
      let cond = (if has_prev { "!((pr : " + w + ") == word(0))" } else { "T" }) +
        (if has_next { " && !((nx : " + w + ") == word(0))" } else { "" })
      ignore(
        sym_prove(
          "tlsf_block_free_unlink_" +
          (if has_prev { "prev" } else { "head" }) +
          "_" +
          (if has_next { "cons" } else { "nil" }) +
          "_all_raw",
          "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ pr : \{w}, ∀ nx : \{w}, ∀ size : \{w}, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{own(pre)}),tlsf_block_free_unlink(d,free_idx),\{mid})",
          [],
          () => [vc],
          afters=if has_prev {
            [out0, mid, @logic.sa_false]
          } else {
            [out0, @logic.sa_false, mid]
          },
          kind="lemma",
        ),
      )
    }
  }
}
