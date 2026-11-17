// Read views of the complete bin table, retaining the entire saved heap.

///|
fn prove_tlsf_find_views() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let base = "word_and(word_add((d : \{w}), word(15)), word(4294967280))"
  let sb_at = (fw : String) => {
    "word_add(word_add(\{base}, word(4)), word_mul(\{fw}, word(68)))"
  }
  let slot_at = (fw : String, jw : String) => {
    "word_add(word_add(\{sb_at(fw)}, word(4)), word_jshl(\{jw}, word(2)))"
  }
  let cell = (at : String, x : String) => {
    "pts(val((\{at} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let ff = "(f : Num) => tlsf_level((d : \{w}), f, (sb : (Num) -> \{w})(f), (bl : \{bt})(f))"
  let f = "val((fw : \{w}))"
  let j = "val((jw : \{w}))"
  let bfr = "(bl : \{bt})(\{f})"
  let row = "(j : Num) => tlsf_slot_item((d : \{w}), (fw : \{w}), j, \{bfr}(j))"
  let levels = "tlsf_istar(\{ff}, 28)"
  let levels_rest = "tlsf_istar((i : Num) => if i == \{f} { emp } else { (\{ff})(i) }, 28)"
  let slots = "tlsf_istar(\{row}, 16)"
  let slots_rest = "tlsf_istar((i : Num) => if i == \{j} { emp } else { (\{row})(i) }, 16)"
  let fp = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
  let focus = (n : String, fun_ : String, k : String) => {
    @bool.undisch(inst(thm("tlsf_istar_focus"), [n, fun_, k]))
  }
  let level_at = @simp.rewr_conv(thm("tlsf_level"))(
    tm("tlsf_level((d : \{w}), \{f}, (sb : (Num) -> \{w})(\{f}), \{bfr})"),
  )
  let item_at = @simp.rewr_conv(thm("tlsf_slot_item"))(
    tm("tlsf_slot_item((d : \{w}), (fw : \{w}), \{j}, \{bfr}(\{j}))"),
  )
  let rws = [thm("tlsf_bins"), thm("has_i32")]
  let focus_f = focus("28", ff, f)
  let focus_j = focus("16", row, j)
  let row_w = "(j : Num) => tlsf_slot_item((d : \{w}), word(\{f}), j, \{bfr}(j))"
  let focus_jw = focus("16", row_w, j)
  let lifts = lift_rws()
  def(
    "tlsf_tables_sync",
    "tlsf_tables_sync((fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})) == (tlsf_sync(fl, 28, (f : Num) => !(sb(f) == word(0))) && (∀ f : Num, f < 28 → tlsf_sync(sb(f), 16, (j : Num) => !(bl(f)(j) == NIL))))",
  )
  let sync = lemma(
    "tlsf_bins_sync",
    "∀ d : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, tlsf_bins(d, fl, sb, bl, h) → tlsf_tables_sync(fl, sb, bl)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_tables_sync")]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.undisch_tac(
                tm(
                  "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (h : \{heap}))",
                ),
              ),
              rw([thm("tlsf_bins")]),
              strip,
              arw([]),
            ]),
            seq([
              @tactics.x_gen_tac(tm("(f : Num)")),
              @tactics.disch_tac,
              @tactics.undisch_tac(
                tm(
                  "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (h : \{heap}))",
                ),
              ),
              rw(
                [
                  thm("tlsf_bins"),
                  focus("28", ff, "(f : Num)"),
                  @simp.rewr_conv(thm("tlsf_level"))(
                    tm(
                      "tlsf_level((d : \{w}), (f : Num), (sb : (Num) -> \{w})(f), (bl : \{bt})(f))",
                    ),
                  ),
                ] +
                lifts,
              ),
              strip,
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
  def(
    "tlsf_ro",
    "tlsf_ro((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (before : \{heap}), (fp : \{rty}), (gs : List[Value]), (ms : Num), (h : \{heap})) == (h == before && star(tlsf_bins(d, fl, sb, bl), fp(gs, ms), h))",
  )
  let ro = thm("tlsf_ro")
  let common = "∀ d : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let states = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}"
  let rh = "tlsf_ro(d, fl, sb, bl, before, fp, gs, ms, h)"
  let root = lemma(
    "tlsf_ro_fl",
    "\{common}, \{states}, \{rh} → has_i32(h, val(\{base}), fl)",
    () => ent_tac([ro] + rws, ["star(\{levels}, \{fp})"]),
  )
  let sb_read = lemma(
    "tlsf_ro_sb",
    "\{common}, ∀ fw : \{w}, val(fw) < 28 → (\{states}, \{rh} → has_i32(h, val(\{sb_at("(fw : \{w})")}), sb(val(fw))))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        ent_tac([ro] + rws + [focus_f, level_at, @words.word_val()], [
          "star(\{cell(base, "fl")}, star(\{slots}, star(\{levels_rest}, \{fp})))",
        ]),
      ])
    },
  )
  let head_read = lemma(
    "tlsf_ro_head",
    "\{common}, ∀ fw : \{w}, ∀ jw : \{w}, val(fw) < 28 && val(jw) < 16 → (\{states}, \{rh} → has_i32(h, val(\{slot_at("(fw : \{w})", "(jw : \{w})")}), tlsf_hd(bl(val(fw))(val(jw)))))",
    () => {
      seq([
        gen,
        strip,
        ent_tac(
          [ro] +
          rws +
          [focus_f, level_at, @words.word_val(), focus_j, focus_jw, item_at],
          [
            "star(\{cell(base, "fl")}, star(\{cell(sb_at("(fw : \{w})"), "sb(\{f})")}, star(tlsf_bin(\{bfr}(\{j})), star(\{slots_rest}, star(\{levels_rest}, \{fp})))))",
          ],
        ),
      ])
    },
  )
  let v = "(v : List[Value])"
  let lc = "(lc : List[Value])"
  let rval = "tlsf_ro((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (before : \{heap}), (fp : \{rty}))"
  let ii = (x : String) => "V_num(ConstInt32(\{x}))"
  let args = [
    "(d : \{w})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  for
    (name, addr, value, vars, hyp, view, inds) in [
      ("st_tlsf_load_fl", base, "(fl : \{w})", "", "", root, []),
      (
        "st_tlsf_load_sb",
        sb_at("(fw : \{w})"),
        "(sb : (Num) -> \{w})(val((fw : \{w})))",
        ", ∀ fw : \{w}",
        "val((fw : \{w})) < 28 → ",
        sb_read,
        ["(fw : \{w})"],
      ),
      (
        "st_tlsf_load_head",
        slot_at("(fw : \{w})", "(jw : \{w})"),
        "tlsf_hd((bl : \{bt})(val((fw : \{w})))(val((jw : \{w}))))",
        ", ∀ fw : \{w}, ∀ jw : \{w}",
        "val((fw : \{w})) < 28 && val((jw : \{w})) < 16 → ",
        head_read,
        ["(fw : \{w})", "(jw : \{w})"],
      ),
    ] {
    let _ = lemma(
      name,
      "\{common}, ∀ v : List[Value], ∀ lc : List[Value]\{vars}, \{hyp}sl_triple(st(APPEND(v, [\{ii(addr)}]), lc, \{rval}), [Load(T_i32, NONE, 2, 0)], st(APPEND(v, [\{ii(value)}]), lc, \{rval}))",
      () => {
        seq([
          gen,
          @tactics.try_tac(strip),
          @tactics.match_mp_tac(
            inst(thm("st_load_read"), [v, lc, rval, addr, value, "2", "0"]),
          ),
          rw([@arith.add_clauses()]),
          if inds.is_empty() {
            @tactics.accept_tac(inst(view, args))
          } else {
            seq([@tactics.match_mp_tac(inst(view, args + inds)), arw([])])
          },
        ])
      },
    )
  }
  ignore(sync)
}
