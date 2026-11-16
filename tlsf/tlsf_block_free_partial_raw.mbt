// The ordinary partial-page path executes the full inlined branch and
// returns without publishing, unlinking, or calling Memory::free.

///|
fn prove_tlsf_block_free_partial_raw() -> Unit raise {
  let w = w32
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let at = (p : String, n : Int32) => "word_add((\{p} : \{w}),word(\{n}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star(ps+["(fp : "+rty+")(gs,ms)"])}"
  }
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ b : \{w}, ∀ p : \{w}, ∀ u : \{w}, ∀ total : \{w}, ∀ head : \{w}, ∀ old : \{w}, ∀ l0 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let before = [
    cell(at("b", 4), "p"),
    cell(at("b", 8), "old"),
    cell(at("p", 20), "head"),
    cell(at("p", 16), "u"),
    cell(at("p", 12), "total"),
  ]
  let after = [
    cell(at("b", 4), "p"),
    cell(at("b", 8), "head"),
    cell(at("p", 20), "b"),
    cell(at("p", 16), "word_sub((u : " + w + "),word(1))"),
    cell(at("p", 12), "total"),
  ]
  let q = "st([\{i("word(0)")}],[\{i("p")},\{i("u")},(l2 : Value)],\{own(after)})"
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
  ignore(
    sym_prove(
      "tlsf_block_free_partial_raw",
      "\{vars}, !(u == total) && !(u == word(1)) → sl_triple(st(NIL,[l0,\{i("b")},l2],\{own(before)}),tlsf_block_free_code(d,free_idx),\{q})",
      [],
      [vc],
      afters=Array::make(5, @logic.sa_false),
      kind="lemma",
    ),
  )
}
