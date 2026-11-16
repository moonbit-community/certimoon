// Word-level triples for the initialization stores. Every byte outside the
// exposed cells, including existing pages and clients, stays in the frame.

///|
fn prove_tlsf_page_allocate_raw() -> Unit raise {
  let w = w32
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let at = (p : String, k : String) => "word_add((\{p} : \{w}),word(\{k}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (cells : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star(cells+["(fp : " + rty + ")(gs,ms)"])}"
  }
  let _ = lemma(
    "st_page_allocate_udiv",
    "∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ a : \{w}, ∀ b : \{w}, !(b == word(0)) → sl_triple(st(APPEND(v,[\{i("a")},\{i("b")}]),l,R),[Binop(T_i32,Binop_i(Div(U)))],st(APPEND(v,[\{i("word_udiv((a : "+w+"),(b : "+w+"))")}]),l,R))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("st_binop")),
      @simp.asm_rewrite_tac(
        ths([
          @wasm.thm("app_binop"),
          @wasm.thm("app_binop_i_v"),
          @wasm.thm("app_binop_i"),
          @wasm.thm("int_div_u"),
          @wasm.thm("map_option"),
        ]),
      ),
    ]),
  )
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let b0 = at(p, "32")
  let total = "word_udiv((word(1056) : \{w}),word_add(\{s},word(8)))"
  let before = [
    cell(at(p, "8"), "w0"),
    cell(at(p, "12"), "w1"),
    cell(at(p, "20"), "w2"),
    cell(at(p, "28"), "w3"),
    cell(b0, "w4"),
    cell(at(b0, "4"), "w5"),
    cell(at(b0, "8"), "w6"),
  ]
  let after = [
    cell(at(p, "8"), s),
    cell(at(p, "12"), total),
    cell(at(p, "20"), b0),
    cell(at(p, "28"), "word(0)"),
    cell(b0, "word(4)"),
    cell(at(b0, "4"), p),
    cell(at(b0, "8"), "word(0)"),
  ]
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ s : \{w}, ∀ l2 : Value, ∀ l3 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}, ∀ w0 : \{w}, ∀ w1 : \{w}, ∀ w2 : \{w}, ∀ w3 : \{w}, ∀ w4 : \{w}, ∀ w5 : \{w}, ∀ w6 : \{w}"
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
      "tlsf_page_allocate_begin_raw",
      "\{vars}, !(word_add(s,word(8)) == word(0)) → sl_triple(st(NIL,[\{i(s)},\{i(p)},l2,l3,l4,l5],\{pred(before)}),tlsf_page_allocate_begin(take_idx),st(NIL,[\{i(s)},\{i(p)},\{i(b0)},\{i("word(1)")},l4,\{i(total)}],\{pred(after)}))",
      [],
      [@meson.asm_meson_tac(ths([])), vc],
      rules=["st_page_allocate_udiv"] + step_rules,
      kind="lemma",
    ),
  )
  let k = "(k : \{w})"
  let head = "(head : \{w})"
  let b = "word_add(\{b0},word_mul(\{k},word_add(\{s},word(8))))"
  let before = [
    cell(b, "w0"),
    cell(at(b, "4"), "w1"),
    cell(at(b, "8"), "w2"),
    cell(at(p, "20"), head),
  ]
  let after = [
    cell(b, "word(4)"),
    cell(at(b, "4"), p),
    cell(at(b, "8"), head),
    cell(at(p, "20"), b),
  ]
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ s : \{w}, ∀ k : \{w}, ∀ head : \{w}, ∀ total : Value, ∀ l4 : Value, ∀ fp : \{rty}, ∀ w0 : \{w}, ∀ w1 : \{w}, ∀ w2 : \{w}"
  ignore(
    sym_prove(
      "tlsf_page_allocate_step_raw",
      "\{vars}, sl_triple(st(NIL,[\{i(s)},\{i(p)},\{i(head)},\{i(k)},l4,total],\{pred(before)}),tlsf_page_allocate_step(take_idx),st([\{i("word_add("+k+",word(1))")}],[\{i(s)},\{i(p)},\{i(b)},\{i(k)},\{i(b)},total],\{pred(after)}))",
      [],
      [vc],
      kind="lemma",
    ),
  )
}
