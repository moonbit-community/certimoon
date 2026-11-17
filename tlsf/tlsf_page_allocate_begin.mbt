// Allocate's first stores expose nine words of arbitrary payload, retaining
// the old used/prev words and all bytes beyond the written slot links.

///|
fn prove_tlsf_page_allocate_begin() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let cap = "(cap : Num)"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let tail = [
    "tlsf_bytes(val((p : \{w}))+44,val((s : \{w}))-4)",
    "tlsf_bytes(val((p : \{w}))+40+val((s : \{w})),cap-32-val((s : \{w})))",
  ]
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star(ps+["(fp : "+rty+")(gs,ms)"])}"
  }
  let frame = own(
    [cell("val((p : \{w}))+16", "w2"), cell("val((p : \{w}))+24", "w4")] + tail,
  )
  let path = inst(
    thm("tlsf_page_allocate_begin_raw"),
    [
      "(take_idx : Num)", p, s, "(l2 : Value)", "(l3 : Value)", "(l4 : Value)", "(l5 : Value)",
      frame,
    ] +
    [0, 1, 3, 5, 6, 7, 8].map(j => "(w\{j} : \{w})"),
  )
  let geom = "tlsf_page_allocate_geometry(\{p},\{cap},val(\{s}))"
  let build = "tlsf_page_allocate_build(\{p},\{cap},val(\{s}),1,(used0 : \{w}),(prev0 : \{w}))"
  let post = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ used0 : \{w}, ∃ prev0 : \{w}, star(\{build},(fp : \{rty})(gs,ms),h)"
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ l2 : Value, ∀ l3 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_page_allocate_begin_build",
    "\{vars}, \{geom} → sl_triple(st(NIL,[\{i(s)},\{i(p)},l2,l3,l4,l5],\{own(["tlsf_bytes(val((p : \{w}))+8,cap)"])}),tlsf_page_allocate_begin(take_idx),st(NIL,[\{i(s)},\{i(p)},\{i("word_add(p,word(32))")},\{i("word(1)")},l4,\{i("word(tlsf_small_total(val((s : \{w}))))")}],\{post}))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.undisch_tac(tm(geom)),
        rw([thm("tlsf_page_allocate_geometry")]),
        strip,
        @tactics.mp_tac(inst(thm("tlsf_page_allocate_total_word"), [s])),
        arw([]),
        strip,
        seq(
          [8, 12, 20, 28, 32].map(n => {
            free_have(
              "val(word_add(\{p},word(\{n}))) == val((p : \{w}))+\{n}",
              seq([
                @tactics.match_mp_tac(thm("val_add_small")),
                @int.asm_arith_tac,
              ]),
            )
          }),
        ),
        seq(
          [4, 8].map(n => {
            free_have(
              "val(word_add(word_add(\{p},word(32)),word(\{n}))) == val((p : \{w}))+\{32+n}",
              seq([
                free_have(
                  "val(word_add(word_add(\{p},word(32)),word(\{n}))) == val(word_add(p,word(32)))+\{n}",
                  seq([
                    @tactics.match_mp_tac(thm("val_add_small")),
                    arw([]),
                    @int.asm_arith_tac,
                  ]),
                ),
                arw([]),
                @int.asm_arith_tac,
              ]),
            )
          }),
        ),
        free_have("4 <= val((s : \{w}))", @int.asm_arith_tac),
        free_have(
          "val((p : \{w}))+44+(val((s : \{w}))-4) == val((p : \{w}))+(40+val(s))",
          @int.asm_arith_tac,
        ),
        free_have(
          "36 <= (cap : Num) && cap-36 == (val((s : \{w}))-4)+(cap-32-val((s : \{w})))",
          @int.asm_arith_tac,
        ),
        free_have(
          "tlsf_bytes(val(\{p})+8,cap) == ((h : \{heap}) => \{Array::makei(9,j => "∃ w\{j} : \{w}, ").join("")}\{small_star(Array::makei(9,j => cell("val((p : \{w}))+\{8+4*j}","w\{j}"))+tail)}(h))",
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_page_allocate_words9"), ["val(" + p + ")+8", cap]),
            ),
            arw([]),
            rw([
              arith("∀ a : Num, ∀ b : Num, ∀ c : Num, a+b+c == a+(b+c)"),
            ]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            rw(
              [
                inst(thm("tlsf_bytes_split"), [
                  "val(" + p + ")+44",
                  "val(" + s + ")-4",
                  "(cap : Num)-32-val((s : \{w}))",
                ]),
              ] +
              lift_rws(),
            ),
            arw(
              [
                arith(
                  "∀ p : Num, ∀ s : Num, 4 <= s → p+44+(s-4) == p+40+s",
                ),
                thm("star_assoc"),
                thm("star_emp_hr"),
              ] +
              lift_rws(),
            ),
          ]),
        ),
        g => {
          let facts = g.0.to_array().map(a => a.1)
          let postrws = [
            thm("tlsf_page_allocate_build"),
            thm("tlsf_page_allocate_istar_one"),
            thm("tlsf_page_allocate_slot"),
            thm("tlsf_page_allocate_head_one"),
            thm("tlsf_page_allocate_slot_zero"),
            thm("tlsf_page_allocate_head"),
            @words.word_val(),
            @arith.add_clauses(),
            @arith.mult_clauses(),
            @arith.sub_0(),
            arith("∀ p : Num, ∀ s : Num, p+32+(8+s) == p+40+s"),
            arith("∀ cap : Num, ∀ s : Num, cap-24-(8+s) == cap-32-s"),
            arith(
              "∀ p : Num, p+32+4 == p+36 && p+32+8 == p+40 && p+32+12 == p+44",
            ),
          ]

          by_path(
            path,
            "T",
            facts,
            ["(w2 : " + w + ")", "(w4 : " + w + ")"],
            facts + postrws,
            Array::makei(9, j => "(w\{j} : \{w})"),
          )(g)
        },
      ])
    },
  )
}
