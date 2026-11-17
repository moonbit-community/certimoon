// One compiled loop iteration extends the initialized prefix by one slot.

///|
fn prove_tlsf_page_allocate_step() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let cap = "(cap : Num)"
  let k = "(k : Num)"
  let b = "tlsf_small_slot(\{p},val(\{s}),\{k})"
  let head = "tlsf_page_allocate_head(\{p},val(\{s}),\{k})"
  let build = (n : String) => {
    "tlsf_page_allocate_build(\{p},\{cap},val(\{s}),\{n},(used0 : \{w}),(prev0 : \{w}))"
  }
  let work = (v0 : String, v1 : String, v2 : String, h : String) => {
    "tlsf_page_allocate_work(\{p},\{cap},val(\{s}),\{k},(used0 : \{w}),(prev0 : \{w}),\{h},(\{v0} : \{w}),(\{v1} : \{w}),(\{v2} : \{w}))"
  }
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star(ps+["(fp : "+rty+")(gs,ms)"])}"
  }
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let frame = own([
    cell("val(p)+8", s),
    cell("val(p)+12", "word(tlsf_small_total(val((s : \{w}))))"),
    cell("val(p)+16", "used0"),
    cell("val(p)+24", "prev0"),
    cell("val(p)+28", "word(0)"),
    "tlsf_istar(tlsf_page_allocate_slot(p,val((s : \{w}))),k)",
    "tlsf_bytes(val(\{b})+12,val((s : \{w}))-4)",
    "tlsf_bytes(val(p)+32+(8+val((s : \{w})))*SUC(k),cap-24-(8+val((s : \{w})))*SUC(k))",
  ])
  let path = inst(thm("tlsf_page_allocate_step_raw"), [
    "(take_idx : Num)",
    p,
    s,
    "(word(k) : " + w + ")",
    head,
    i("word(tlsf_small_total(val(" + s + ")))"),
    "(l4 : Value)",
    frame,
    "(w0 : " + w + ")",
    "(w1 : " + w + ")",
    "(w2 : " + w + ")",
  ])
  let geom = "tlsf_page_allocate_geometry(\{p},\{cap},val(\{s}))"
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ k : Num, ∀ used0 : \{w}, ∀ prev0 : \{w}, ∀ l4 : Value, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_page_allocate_step_build",
    "\{vars}, \{geom} && k < tlsf_small_total(val((s : \{w}))) → sl_triple(st(NIL,[\{i(s)},\{i(p)},\{i(head)},\{i("word(k)")},l4,\{i("word(tlsf_small_total(val((s : \{w}))))")}],\{own([build(k)])}),tlsf_page_allocate_step(take_idx),st([\{i("word(SUC(k))")}],[\{i(s)},\{i(p)},\{i(b)},\{i("word(k)")},\{i(b)},\{i("word(tlsf_small_total(val((s : \{w}))))")}],\{own([build("SUC(k)")])}))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_page_allocate_bounds"), [p, cap, "val(" + s + ")", k]),
        ),
        arw([]),
        strip,
        free_have(
          "word_add(word_add(\{p},word(32)),word_mul(word(k),word_add(\{s},word(8)))) == \{b}",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_page_allocate_slot_word"), [p, cap, s, k]),
            ),
            arw([]),
          ]),
        ),
        free_have(
          "val(word_add(\{b},word(4))) == val(\{b})+4 && val(word_add(\{b},word(8))) == val(\{b})+8 && val(word_add(\{p},word(20))) == val(p)+20",
          seq([
            @tactics.undisch_tac(tm(geom)),
            rw([thm("tlsf_page_allocate_geometry")]),
            strip,
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.match_mp_tac(thm("val_add_small")),
            @int.asm_arith_tac,
          ]),
        ),
        free_have(
          "word_add((word(k) : \{w}),word(1)) == word(SUC(k))",
          seq([rw([@equal.gsym(@words.word_add_v1()), @arith.add1()])]),
        ),
        free_have(
          "\{build(k)} == ((h : \{heap}) => ∃ w0 : \{w}, ∃ w1 : \{w}, ∃ w2 : \{w}, \{work("w0","w1","w2",head)}(h))",
          seq([
            @tactics.match_mp_tac(thm("tlsf_page_allocate_work_open")),
            arw([]),
          ]),
        ),
        free_have(
          "\{build("SUC(k)")} == \{work("word(4)",p,head,b)}",
          seq([
            @tactics.conv_tac(@equal.sym_conv),
            @tactics.match_mp_tac(thm("tlsf_page_allocate_work_close")),
            arw([]),
          ]),
        ),
        g => {
          let facts = g.0.to_array().map(a => a.1)
          by_path(
            path,
            "T",
            facts + [thm("tlsf_page_allocate_work"), @words.word_val()],
            [],
            facts + [thm("tlsf_page_allocate_work"), @words.word_val()],
            ["(w0 : " + w + ")", "(w1 : " + w + ")", "(w2 : " + w + ")"],
          )(g)
        },
      ])
    },
  )
}
