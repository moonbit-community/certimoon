// The complete TLSF free-list table: 28 levels of 16 bins, with both
// bitmap levels synchronized to the bin lists. The table owns its words
// and the lists' links; size/flag words remain outside it, for the
// physical-chain invariant to connect to this model later.
//
// Focus one bin with tlsf_istar_focus, apply tlsf_push or tlsf_pop, then
// fold it back up with the updated bitmaps. All other bins and levels,
// and the caller's heap/globals/size assertion, remain in the frame.

///|
fn prove_tlsf_all_bins() -> Unit raise {
  let w = w32
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let fty = "(Num) -> \{hprop}"
  // an iterated separating conjunction: F(0) * ... * F(n - 1)
  def(
    "tlsf_istar",
    "tlsf_istar((ff : \{fty}), 0) == emp && tlsf_istar(ff, SUC(n)) == star(tlsf_istar(ff, n), ff(n))",
  )
  let istar = thm("tlsf_istar")
  let cong = lemma(
    "tlsf_istar_cong",
    "∀ n : Num, ∀ ff : \{fty}, ∀ gg : \{fty}, (∀ i : Num, i < n → ff(i) == gg(i)) → tlsf_istar(ff, n) == tlsf_istar(gg, n)",
    () => {
      seq([
        @nums.induct_tac,
        rw([istar]),
        gen,
        @tactics.disch_tac,
        have(
          "(ff : \{fty})(n) == (gg : \{fty})(n)",
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @int.arith_tac,
          ]),
        ),
        have(
          "tlsf_istar((ff : \{fty}), n) == tlsf_istar((gg : \{fty}), n)",
          seq([
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @tactics.gen_tac,
            @tactics.disch_tac,
            @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
            @int.asm_arith_tac,
          ]),
        ),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_istar_focus",
    "∀ n : Num, ∀ ff : \{fty}, ∀ k : Num, k < n → tlsf_istar(ff, n) == star(ff(k), tlsf_istar((i : Num) => if i == k { emp } else { ff(i) }, n))",
    () => {
      seq([
        @nums.induct_tac,
        rw([istar, @arith.lt()]),
        gen,
        @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
        // k = n
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.first_x_assum(th => @tactics.subst1_tac(th)),
                rw([]),
                have(
                  "tlsf_istar((i : Num) => if i == n { emp } else { (ff : \{fty})(i) }, n) == tlsf_istar(ff, n)",
                  seq([
                    @tactics.match_mp_tac(cong),
                    @tactics.gen_tac,
                    @tactics.disch_tac,
                    have("!((i : Num) == n)", @int.asm_arith_tac),
                    arw([]),
                  ]),
                ),
                arw([thm("star_emp_hr")]),
                @tactics.match_accept_tac(thm("star_comm")),
              ]),
            ),
            // k < n
            solve(
              seq([
                have("!((n : Num) == k)", @int.asm_arith_tac),
                @tactics.first_x_assum(th => {
                  @tactics.mp_tac(@bool.spec(tm("(ff : \{fty})"), th))
                }),
                @tactics.disch_then(th => {
                  @tactics.mp_tac(@bool.spec(tm("(k : Num)"), th))
                }),
                arw([]),
                @tactics.disch_tac,
                arw([thm("star_assoc")]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let focus = thm("tlsf_istar_focus")
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let base = "word_and(word_add(d, word(15)), word(4294967280))"
  let sl_at = (fw : String) => {
    "word_add(word_add(\{base}, word(4)), word_mul(\{fw}, word(68)))"
  }
  let slot_at = (fw : String, jw : String) => {
    "word_add(word_add(\{sl_at(fw)}, word(4)), word_jshl(\{jw}, word(2)))"
  }
  let lw = "List[\{w}]"
  // the table: the first-level bitmap, then for each of the 28 levels its
  // bitmap and 16 bins, a bin's head word and its list
  def(
    "tlsf_upd", "tlsf_upd((ff : (Num) -> A), (k : Num), (v : A)) == ((i : Num) => if i == k { v } else { ff(i) })",
  )
  let upd = thm("tlsf_upd")
  def(
    "tlsf_slot_item",
    "tlsf_slot_item((d : \{w}), (fw : \{w}), (j : Num), (xs : \{lw})) == star(\{cell(slot_at("fw", "word(j)"), "tlsf_hd(xs)")}, tlsf_bin(xs))",
  )
  def(
    "tlsf_level",
    "tlsf_level((d : \{w}), (f : Num), (s : \{w}), (L : (Num) -> \{lw})) == ((h : \{heap}) => tlsf_sync(s, 16, (j : Num) => !(L(j) == NIL)) && star(\{cell(sl_at("word(f)"), "s")}, tlsf_istar((j : Num) => tlsf_slot_item(d, word(f), j, L(j)), 16), h))",
  )
  def(
    "tlsf_bins",
    "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : (Num) -> (Num) -> \{lw})) == ((h : \{heap}) => tlsf_sync(fl, 28, (f : Num) => !(sb(f) == word(0))) && star(\{cell(base, "fl")}, tlsf_istar((f : Num) => tlsf_level(d, f, sb(f), bl(f)), 28), h))",
  )
  let upd_same = lemma(
    "tlsf_upd_same",
    "∀ ff : (Num) -> A, ∀ k : Num, ∀ v : A, tlsf_upd(ff, k, v)(k) == v",
    () => seq([gen, rw([upd])]),
  )
  let rest_tac = seq([
    gen,
    rw([@class.fun_eq_thm()]),
    @tactics.gen_tac,
    @class.cond_cases_tac,
    arw([upd]),
  ])
  let level_rest = lemma(
    "tlsf_level_rest",
    "∀ d : \{w}, ∀ k : Num, ∀ sb : (Num) -> \{w}, ∀ v : \{w}, ∀ bl : (Num) -> (Num) -> \{lw}, ∀ L : (Num) -> \{lw}, ((i : Num) => if i == k { emp } else { tlsf_level(d, i, tlsf_upd(sb, k, v)(i), tlsf_upd(bl, k, L)(i)) }) == ((i : Num) => if i == k { emp } else { tlsf_level(d, i, sb(i), bl(i)) })",
    () => rest_tac,
  )
  let item_rest = lemma(
    "tlsf_item_rest",
    "∀ d : \{w}, ∀ fw : \{w}, ∀ k : Num, ∀ L : (Num) -> \{lw}, ∀ xs : \{lw}, ((j : Num) => if j == k { emp } else { tlsf_slot_item(d, fw, j, tlsf_upd(L, k, xs)(j)) }) == ((j : Num) => if j == k { emp } else { tlsf_slot_item(d, fw, j, L(j)) })",
    () => rest_tac,
  )
  let bit_nz = lemma(
    "tlsf_or_bit_nz",
    "∀ x : \{w}, ∀ j : \{w}, !(word_or(x, word_jshl(word(1), j)) == word(0))",
    () => {
      seq([
        gen,
        rw([
          @words.word_eq_bits(),
          @words.bit_word_or(),
          @words.word_jshl(),
          @words.bit_word_shl(),
          @words.bit_word_1(),
          @words.bit_word_0(),
          @words.dimindex_32(),
          @class.not_forall_thm(),
        ]),
        @tactics.exists_tac(tm("MOD(val((j : \{w})), 32)")),
        @int.arith_tac,
      ])
    },
  )
  let sync_set = thm("tlsf_sync_set")
  let _ = lemma(
    "tlsf_sync_push_bin",
    "∀ s : \{w}, ∀ j : \{w}, ∀ L : (Num) -> \{lw}, ∀ m : \{w}, val(j) < 16 && tlsf_sync(s, 16, (i : Num) => !(L(i) == NIL)) → tlsf_sync(word_or(s, word_jshl(word(1), j)), 16, (i : Num) => !(tlsf_upd(L, val(j), CONS(m, L(val(j))))(i) == NIL))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        have(
          "((i : Num) => !(tlsf_upd((L : (Num) -> \{lw}), val((j : \{w})), CONS((m : \{w}), L(val(j))))(i) == NIL)) == ((i : Num) => i == val(j) || !(L(i) == NIL))",
          seq([
            rw([@class.fun_eq_thm()]),
            @tactics.gen_tac,
            rw([upd]),
            @class.cond_cases_tac,
            arw([@lists.not_cons_nil()]),
          ]),
        ),
        arw([]),
        @tactics.match_mp_tac(sync_set),
        arw([]),
        @int.arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_sync_push_top",
    "∀ fl : \{w}, ∀ f : \{w}, ∀ j : \{w}, ∀ sb : (Num) -> \{w}, val(f) < 28 && tlsf_sync(fl, 28, (i : Num) => !(sb(i) == word(0))) → tlsf_sync(word_or(fl, word_jshl(word(1), f)), 28, (i : Num) => !(tlsf_upd(sb, val(f), word_or(sb(val(f)), word_jshl(word(1), j)))(i) == word(0)))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        have(
          "((i : Num) => !(tlsf_upd((sb : (Num) -> \{w}), val((f : \{w})), word_or(sb(val(f)), word_jshl(word(1), (j : \{w}))))(i) == word(0))) == ((i : Num) => i == val(f) || !(sb(i) == word(0)))",
          seq([
            rw([@class.fun_eq_thm()]),
            @tactics.gen_tac,
            rw([upd]),
            @class.cond_cases_tac,
            arw([bit_nz]),
          ]),
        ),
        arw([]),
        @tactics.match_mp_tac(sync_set),
        arw([]),
        @int.arith_tac,
      ])
    },
  )
  // Replacing an occupied entry either keeps its bit or clears it.
  let sync_replace = lemma(
    "tlsf_sync_replace",
    "∀ s : \{w}, ∀ j : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, ∀ b : Bool, val(j) < n && n <= 32 && tlsf_sync(s, n, ne) && ne(val(j)) → tlsf_sync((if b { s } else { word_xor(s, word_jshl(word(1), j)) }), n, (k : Num) => if k == val(j) { b } else { ne(k) })",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @class.asm_cases_tac(tm("(b : Bool)")),
        arw([]),
        have(
          "((k : Num) => if k == val((j : \{w})) { T } else { (ne : (Num) -> Bool)(k) }) == ne",
          seq([
            rw([@class.fun_eq_thm()]),
            @tactics.gen_tac,
            @class.cond_cases_tac,
            arw([]),
          ]),
        ),
        arw([]),
        have(
          "((k : Num) => if k == val((j : \{w})) { F } else { (ne : (Num) -> Bool)(k) }) == ((k : Num) => !(k == val(j)) && ne(k))",
          seq([
            rw([@class.fun_eq_thm()]),
            @tactics.gen_tac,
            @class.cond_cases_tac,
            arw([]),
          ]),
        ),
        arw([]),
        @tactics.match_mp_tac(thm("tlsf_sync_clear")),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_sync_pop_bin",
    "∀ s : \{w}, ∀ j : \{w}, ∀ L : (Num) -> \{lw}, ∀ xs : \{lw}, val(j) < 16 && tlsf_sync(s, 16, (i : Num) => !(L(i) == NIL)) && !(L(val(j)) == NIL) → tlsf_sync((if xs == NIL { word_xor(s, word_jshl(word(1), j)) } else { s }), 16, (i : Num) => !(tlsf_upd(L, val(j), xs)(i) == NIL))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        have(
          "((i : Num) => !(tlsf_upd((L : (Num) -> \{lw}), val((j : \{w})), (xs : \{lw}))(i) == NIL)) == ((i : Num) => if i == val(j) { !(xs == NIL) } else { !(L(i) == NIL) })",
          seq([
            rw([@class.fun_eq_thm(), upd]),
            @tactics.gen_tac,
            @class.cond_cases_tac,
            arw([]),
          ]),
        ),
        arw([]),
        @tactics.mp_tac(
          inst(sync_replace, [
            "(s : \{w})",
            "(j : \{w})",
            "16",
            "(i : Num) => !((L : (Num) -> \{lw})(i) == NIL)",
            "!((xs : \{lw}) == NIL)",
          ]),
        ),
        arw([arith("16 <= 32")]),
        @class.asm_cases_tac(tm("(xs : \{lw}) == NIL")),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_sync_pop_top",
    "∀ fl : \{w}, ∀ f : \{w}, ∀ sb : (Num) -> \{w}, ∀ s : \{w}, val(f) < 28 && tlsf_sync(fl, 28, (i : Num) => !(sb(i) == word(0))) && !(sb(val(f)) == word(0)) → tlsf_sync((if s == word(0) { word_xor(fl, word_jshl(word(1), f)) } else { fl }), 28, (i : Num) => !(tlsf_upd(sb, val(f), s)(i) == word(0)))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        have(
          "((i : Num) => !(tlsf_upd((sb : (Num) -> \{w}), val((f : \{w})), (s : \{w}))(i) == word(0))) == ((i : Num) => if i == val(f) { !(s == word(0)) } else { !(sb(i) == word(0)) })",
          seq([
            rw([@class.fun_eq_thm(), upd]),
            @tactics.gen_tac,
            @class.cond_cases_tac,
            arw([]),
          ]),
        ),
        arw([]),
        @tactics.mp_tac(
          inst(sync_replace, [
            "(fl : \{w})",
            "(f : \{w})",
            "28",
            "(i : Num) => !((sb : (Num) -> \{w})(i) == word(0))",
            "!((s : \{w}) == word(0))",
          ]),
        ),
        arw([arith("28 <= 32")]),
        @class.asm_cases_tac(tm("(s : \{w}) == word(0)")),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_sync_occupied_nz",
    "∀ s : \{w}, ∀ n : Num, ∀ ne : (Num) -> Bool, ∀ k : Num, tlsf_sync(s, n, ne) && k < n && ne(k) → !(s == word(0))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.mp_tac(
          inst(thm("tlsf_sync_zero"), [
            "(s : \{w})",
            "(n : Num)",
            "(ne : (Num) -> Bool)",
          ]),
        ),
        arw([]),
        @meson.asm_meson_tac(ths([])),
      ])
    },
  )
  let pop_bitmap = lemma(
    "tlsf_pop_bitmap",
    "∀ fl : \{w}, ∀ s : \{w}, ∀ f : \{w}, ∀ j : \{w}, ∀ empty : Bool, !(s == word(0)) → (if empty { if word_xor(s, word_jshl(word(1), j)) == word(0) { word_xor(fl, word_jshl(word(1), f)) } else { fl } } else { fl }) == (if (if empty { word_xor(s, word_jshl(word(1), j)) } else { s }) == word(0) { word_xor(fl, word_jshl(word(1), f)) } else { fl })",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @class.asm_cases_tac(tm("(empty : Bool)")),
        arw([]),
      ])
    },
  )
  // push against the whole table
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let z = i("word(0)")
  let at = (a : String, k : String) => "word_add(\{a}, word(\{k}))"
  let sz = "word_and((hd : \{w}), word(4294967292))"
  let f4 = "(word_sub(word(27), word(word_clz(\{sz}))) : \{w})"
  let sli = "word_and(word_jushr(\{sz}, \{f4}), word(15))"
  let fv = "val((\{f4} : \{w}))"
  let jv = "val(\{sli})"
  let sbt = "(sb : (Num) -> \{w})"
  let blt = "(bl : (Num) -> (Num) -> \{lw})"
  let dt = "(d : \{w})"
  let mt = "(m : \{w})"
  let bit = (j : String) => "word_jshl(word(1), \{j})"
  let chain = (cells : Array[String]) => {
    let mut acc = "fp(gs, ms)"
    for k = cells.length() - 1; k >= 1; k = k - 1 {
      acc = "star(\{cells[k]}, \{acc})"
    }
    "star(\{cells[0]}, \{acc}, h)"
  }
  let state = (v : String, l : String, cells : Array[String]) => {
    "st(\{v}, \{l}, (gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{chain(cells)})"
  }
  let anyl = (v : String, cells : Array[String]) => {
    "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == \{v} && \{chain(cells)}"
  }
  let s2 = "tlsf_upd(\{sbt}, \{fv}, word_or(sb(\{fv}), \{bit(sli)}))"
  let xs2 = "tlsf_upd(\{blt}(\{fv}), \{jv}, CONS(\{mt}, bl(\{fv})(\{jv})))"
  let l2 = "tlsf_upd(\{blt}, \{fv}, \{xs2})"
  let fl2 = "word_or((fl : \{w}), \{bit(f4)})"
  let level_f = (sbx : String, blx : String) => {
    "(f : Num) => tlsf_level(\{dt}, f, \{sbx}(f), \{blx}(f))"
  }
  let items = (xs : String) => {
    "(j : Num) => tlsf_slot_item(\{dt}, \{f4}, j, \{xs}(j))"
  }
  let items_w = (xs : String) => {
    "(j : Num) => tlsf_slot_item(\{dt}, word(\{fv}), j, \{xs}(j))"
  }
  let focus_at = (n : String, ff : String, k : String) => {
    @bool.undisch(inst(focus, [n, ff, k]))
  }
  // a definition's equation at exactly this term
  let def_at = (name : String, t : String) => @simp.rewr_conv(thm(name))(tm(t))
  let level_at = (s : String, xs : String) => {
    def_at("tlsf_level", "tlsf_level(\{dt}, \{fv}, \{s}, \{xs})")
  }
  let item_at = (xs : String) => {
    def_at("tlsf_slot_item", "tlsf_slot_item(\{dt}, \{f4}, \{jv}, \{xs})")
  }
  let rest = "star(tlsf_istar((j : Num) => if j == \{jv} { emp } else { tlsf_slot_item(\{dt}, \{f4}, j, \{blt}(\{fv})(j)) }, 16), tlsf_istar((k : Num) => if k == \{fv} { emp } else { tlsf_level(\{dt}, k, \{sbt}(k), \{blt}(k)) }, 28))"
  let c = "tlsf_sync((fl : \{w}), 28, (f : Num) => !(\{sbt}(f) == word(0))) && tlsf_sync(\{sbt}(\{fv}), 16, (j : Num) => !(\{blt}(\{fv})(j) == NIL))"
  // the lemma `name` for `args`, its hypotheses (a conjunction) assumed:
  // they are the goal's assumptions where it is used
  let under_hyps = (name : String, args : Array[String], hyps : Array[String]) => {
    let mut h = @kernel.assume_rule(tm(hyps[hyps.length() - 1]))
    for k = hyps.length() - 2; k >= 0; k = k - 1 {
      h = @bool.conj(@kernel.assume_rule(tm(hyps[k])), h)
    }
    @bool.mp(@equal.beta_rule(inst(thm(name), args)), h)
  }
  let sync_bin = under_hyps(
    "tlsf_sync_push_bin",
    ["\{sbt}(\{fv})", sli, "\{blt}(\{fv})", mt],
    [
      "\{jv} < 16",
      "tlsf_sync(\{sbt}(\{fv}), 16, (j : Num) => !(\{blt}(\{fv})(j) == NIL))",
    ],
  )
  let sync_top = under_hyps(
    "tlsf_sync_push_top",
    ["(fl : \{w})", f4, sli, sbt],
    [
      "\{fv} < 28",
      "tlsf_sync((fl : \{w}), 28, (f : Num) => !(\{sbt}(f) == word(0)))",
    ],
  )
  let pre_rws = [
    thm("tlsf_bins"),
    focus_at("28", level_f(sbt, blt), fv),
    level_at("\{sbt}(\{fv})", "\{blt}(\{fv})"),
    focus_at("16", items("\{blt}(\{fv})"), jv),
    focus_at("16", items_w("\{blt}(\{fv})"), jv),
    item_at("\{blt}(\{fv})(\{jv})"),
    @words.word_val(),
  ]
  let post_rws = [
    thm("tlsf_bins"),
    focus_at("28", level_f(s2, l2), fv),
    upd_same,
    level_rest,
    level_at("word_or(\{sbt}(\{fv}), \{bit(sli)})", xs2),
    focus_at("16", items(xs2), jv),
    focus_at("16", items_w(xs2), jv),
    item_rest,
    item_at("CONS(\{mt}, \{blt}(\{fv})(\{jv}))"),
    @words.word_val(),
    thm("tlsf_hd"),
    sync_bin,
    sync_top,
  ]
  let path = inst(thm("tlsf_push"), [
    dt,
    mt,
    "(hd : \{w})",
    "(pf0 : \{w})",
    "(nf0 : \{w})",
    "(fl : \{w})",
    "\{sbt}(\{fv})",
    "\{blt}(\{fv})(\{jv})",
    "(gs : List[Value]) => (ms : Num) => star(\{rest}, (fp : \{rty})(gs, ms))",
  ])
  ignore(
    lemma(
      "tlsf_push_all",
      "∀ d : \{w}, ∀ m : \{w}, ∀ hd : \{w}, ∀ pf0 : \{w}, ∀ nf0 : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : (Num) -> (Num) -> \{lw}, ∀ fp : \{rty}, !(m == word(0)) && 16 <= val(\{sz}) → sl_triple(\{state("(NIL : List[Value])", "[\{i("m")}, \{z}, \{z}, \{z}]", [cell("m", "hd"), cell(at("m", "8"), "pf0"), cell(at("m", "12"), "nf0"), "tlsf_bins(d, fl, sb, bl)"])}, tlsf_push_code(d), \{anyl("[\{z}]", [cell("m", "hd"), "tlsf_bins(d, \{fl2}, \{s2}, \{l2})"])})",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.mp_tac(inst(thm("tlsf_code_bounds"), [sz])),
          arw([]),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          by_path(path, c, pre_rws, [], post_rws, []),
        ])
      },
      kind="example",
    ),
  )
  // Pop from any position in the selected bin. The rest of both tables
  // is framed out, just as for push.
  let ys = "(ys : \{lw})"
  let zs = "(zs : \{lw})"
  let before = "APPEND(\{ys}, CONS(\{mt}, \{zs}))"
  let after = "APPEND(\{ys}, \{zs})"
  let sbpop = "(if \{after} == NIL { word_xor(\{sbt}(\{fv}), \{bit(sli)}) } else { \{sbt}(\{fv}) })"
  let flpop = "(if \{after} == NIL { if word_xor(\{sbt}(\{fv}), \{bit(sli)}) == word(0) { word_xor((fl : \{w}), \{bit(f4)}) } else { fl } } else { fl })"
  let spop = "tlsf_upd(\{sbt}, \{fv}, \{sbpop})"
  let rowpop = "tlsf_upd(\{blt}(\{fv}), \{jv}, \{after})"
  let lpop = "tlsf_upd(\{blt}, \{fv}, \{rowpop})"
  let occupied = "!(\{blt}(\{fv})(\{jv}) == NIL)"
  let sbnz = "!(\{sbt}(\{fv}) == word(0))"
  let sync_pop_bin = under_hyps(
    "tlsf_sync_pop_bin",
    ["\{sbt}(\{fv})", sli, "\{blt}(\{fv})", after],
    [
      "\{jv} < 16",
      "tlsf_sync(\{sbt}(\{fv}), 16, (j : Num) => !(\{blt}(\{fv})(j) == NIL))",
      occupied,
    ],
  )
  let sync_pop_top = under_hyps(
    "tlsf_sync_pop_top",
    ["(fl : \{w})", f4, sbt, sbpop],
    [
      "\{fv} < 28",
      "tlsf_sync((fl : \{w}), 28, (f : Num) => !(\{sbt}(f) == word(0)))",
      sbnz,
    ],
  )
  let occupied_nz = under_hyps(
    "tlsf_sync_occupied_nz",
    ["\{sbt}(\{fv})", "16", "(j : Num) => !(\{blt}(\{fv})(j) == NIL)", jv],
    [
      "tlsf_sync(\{sbt}(\{fv}), 16, (j : Num) => !(\{blt}(\{fv})(j) == NIL))",
      "\{jv} < 16",
      occupied,
    ],
  )
  let pop_pre_rws = pre_rws +
    [@kernel.assume_rule(tm("\{blt}(\{fv})(\{jv}) == \{before}"))]
  let pop_post_rws = [
    thm("tlsf_bins"),
    focus_at("28", level_f(spop, lpop), fv),
    upd_same,
    level_rest,
    level_at(sbpop, rowpop),
    focus_at("16", items(rowpop), jv),
    focus_at("16", items_w(rowpop), jv),
    item_rest,
    item_at(after),
    @words.word_val(),
    @bool.prove_hyp(
      occupied_nz,
      @bool.undisch(
        inst(pop_bitmap, [
          "(fl : \{w})",
          "\{sbt}(\{fv})",
          f4,
          sli,
          "\{after} == NIL",
        ]),
      ),
    ),
    sync_pop_bin,
    @bool.prove_hyp(occupied_nz, sync_pop_top),
  ]
  let pop_path = inst(thm("tlsf_pop"), [
    dt,
    mt,
    "(hd : \{w})",
    "(fl : \{w})",
    "\{sbt}(\{fv})",
    ys,
    zs,
    "(gs : List[Value]) => (ms : Num) => star(\{rest}, (fp : \{rty})(gs, ms))",
  ])
  ignore(
    lemma(
      "tlsf_pop_all",
      "∀ d : \{w}, ∀ m : \{w}, ∀ hd : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : (Num) -> (Num) -> \{lw}, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ fp : \{rty}, 16 <= val(\{sz}) && \{blt}(\{fv})(\{jv}) == \{before} → sl_triple(\{state("(NIL : List[Value])", "[\{i("m")}, \{z}, \{z}, \{z}, \{z}]", [cell("m", "hd"), "tlsf_bins(d, fl, sb, bl)"])}, tlsf_pop_code(d), \{anyl("(NIL : List[Value])", [cell("m", "hd"), cell(at("m", "8"), "tlsf_prev(\{ys})"), cell(at("m", "12"), "tlsf_hd(\{zs})"), "tlsf_bins(d, \{flpop}, \{spop}, \{lpop})"])})",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.mp_tac(inst(thm("tlsf_code_bounds"), [sz])),
          arw([]),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          have(occupied, arw([@lists.append_eq_nil(), @lists.not_cons_nil()])),
          by_path(pop_path, c, pop_pre_rws, [], pop_post_rws, []),
        ])
      },
      kind="example",
    ),
  )
}
