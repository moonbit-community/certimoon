// Symbolically execute the shipped read-only search block against the bin table.

///|
fn prove_tlsf_find_query() -> Unit raise {
  let w = w32
  let bt = "(Num) -> (Num) -> List[\{w}]"
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let z = i("word(0)")
  let val = (x : String) => "val((\{x} : \{w}))"
  let cut = (k : String) => "tlsf_cut(\{k})"
  let ct = (x : String) => "(word(word_ctz(\{x})) : \{w})"
  let ss = "(s : \{w})"
  def(
    "tlsf_align",
    "tlsf_align(\{ss}) == word_and(word_add(s, word(15)), word(4294967280))",
  )
  let fword = lemma(
    "tlsf_fword_code",
    "∀ x : \{w}, word_sub(word_sub(word(31), word(word_clz(x))), word(4)) == word_sub(word(27), word(word_clz(x)))",
    @tactics.then_tac(@tactics.gen_tac, g => {
      @tactics.accept_tac(@words.word_rule(g.1))(g)
    }),
  )
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let mask = "word_sub(word_jshl(word(1), word_sub(word(27), word(word_clz(\{ss})))), word(1))"
  let _ = lemma(
    "tlsf_round_code",
    "∀ s : \{w}, word_and(word_add(\{mask}, s), word_xor(\{mask}, word(4294967295))) == tlsf_round(s)",
    seq([
      @tactics.gen_tac,
      rw([
        thm("tlsf_round"),
        thm("tlsf_mask"),
        thm("tlsf_fli"),
        @wasm.thm("int_clz"),
        fword,
        thm("tlsf_xor_ones"),
        @words.word_add_sym(),
      ]),
    ]),
  )
  def(
    "tlsf_search_f",
    "tlsf_search_f(\{ss}) == (word_sub(word(27), word(word_clz(tlsf_round(tlsf_align(s))))) : \{w})",
  )
  def(
    "tlsf_search_j",
    "tlsf_search_j(\{ss}) == word_and(word_jushr(tlsf_round(tlsf_align(s)), tlsf_search_f(s)), word(15))",
  )
  let ff = ct("word_and((fl : \{w}), \{cut("tlsf_search_f(s)")})")
  let jj = ct(
    "word_and((sb : (Num) -> \{w})(\{val(ff)}), \{cut("tlsf_search_j(s)")})",
  )
  let gg = ct(
    "word_and((fl : \{w}), word_jshl(\{cut("tlsf_search_f(s)")}, word(1)))",
  )
  let kk = ct("(sb : (Num) -> \{w})(\{val(gg)})")
  let neq = (a : String) => "!(\{a} == word(32))"
  let domain = "(\{neq(ff)} → \{val(ff)} < 28) && (\{neq(ff)} && \{neq(jj)} → \{val(jj)} < 16) && (\{neq(gg)} → \{val(gg)} < 28) && (\{neq(gg)} && \{neq(kk)} → \{val(kk)} < 16)"
  def(
    "tlsf_search_domain",
    "tlsf_search_domain(\{ss}, (fl : \{w}), (sb : (Num) -> \{w})) == (\{domain})",
  )
  def(
    "tlsf_search",
    "tlsf_search(\{ss}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})) == (if \{ff} == word(32) { word(0) } else { if \{jj} == word(32) { if \{gg} == word(32) { word(0) } else { if \{kk} == word(32) { word(0) } else { tlsf_hd(bl(\{val(gg)})(\{val(kk)})) } } } else { tlsf_hd(bl(\{val(ff)})(\{val(jj)})) } })",
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let nn = "(f : Num) => !((sb : (Num) -> \{w})(f) == word(0))"
  let root_range = (mask : String) => {
    seq([
      @tactics.match_mp_tac(
        inst(thm("tlsf_ctz_range"), ["(fl : \{w})", mask, "28", nn]),
      ),
      arw([]),
    ])
  }
  let row_sync = (fw : String) => {
    have(
      "tlsf_sync((sb : (Num) -> \{w})(\{val(fw)}), 16, (j : Num) => !((bl : \{bt})(\{val(fw)})(j) == NIL))",
      seq([
        @tactics.first_x_assum(th => {
          @tactics.match_mp_tac(@bool.spec(tm(val(fw)), th))
        }),
        arw([]),
      ]),
    )
  }
  let second_range = seq([
    strip,
    have("\{val(ff)} < 28", root_range(cut("tlsf_search_f(s)"))),
    row_sync(ff),
    @tactics.match_mp_tac(
      inst(thm("tlsf_ctz_range"), [
        "(sb : (Num) -> \{w})(\{val(ff)})",
        cut("tlsf_search_j(s)"),
        "16",
        "(j : Num) => !((bl : \{bt})(\{val(ff)})(j) == NIL)",
      ]),
    ),
    arw([]),
  ])
  let fallback_range = seq([
    strip,
    have(
      "\{val(gg)} < 28",
      root_range("word_jshl(\{cut("tlsf_search_f(s)")}, word(1))"),
    ),
    row_sync(gg),
    @tactics.match_mp_tac(
      inst(thm("tlsf_ctz_plain_range"), [
        "(sb : (Num) -> \{w})(\{val(gg)})",
        "16",
        "(j : Num) => !((bl : \{bt})(\{val(gg)})(j) == NIL)",
      ]),
    ),
    arw([]),
  ])
  let _ = lemma(
    "tlsf_search_domain_sync",
    "∀ s : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, tlsf_tables_sync(fl, sb, bl) → tlsf_search_domain(s, fl, sb)",
    seq([
      gen,
      rw([thm("tlsf_tables_sync"), thm("tlsf_search_domain")]),
      strip,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@tactics.disch_tac, root_range(cut("tlsf_search_f(s)"))]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              second_range,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.disch_tac,
                    root_range("word_jshl(\{cut("tlsf_search_f(s)")}, word(1))"),
                  ]),
                  fallback_range,
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let ro = "tlsf_ro((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (before : \{heap}), (fp : \{rty}))"
  let query = "tlsf_search(\{ss}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let vars = "∀ s : \{w}, ∀ d : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(3, lc) == \{i("tlsf_align(s)")} && vs == [\{i(query)}] && \{ro}(gs, ms, h)"
  let after = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ ll : List[Value], \{query} == word(0) && st(NIL, ll, (gg : List[Value]) => (mm : Num) => (hh : \{heap}) => LENGTH(ll) == 6 && EL(3, ll) == \{i("tlsf_align(s)")} && \{ro}(gg, mm, hh), vs, lc, gs, ms, h)"
  let rws = [
    @equal.gsym(thm("tlsf_align")),
    thm("tlsf_round_code"),
    fword,
    @equal.gsym(thm("tlsf_search_f")),
    @equal.gsym(thm("tlsf_search_j")),
    @equal.gsym(thm("tlsf_cut")),
    thm("tlsf_search"),
    thm("tlsf_search_domain"),
    @lists.el(),
    @lists.hd(),
    @lists.tl(),
    @lists.length(),
  ]
  let stmt = "\{vars}, tlsf_search_domain(s, fl, sb) → sl_triple(st(NIL, [\{i(ss)}, \{z}, \{z}, \{z}, \{z}, \{z}], \{ro}), tlsf_find_code(d), \{post})"
  let rules = ["st_tlsf_load_fl", "st_tlsf_load_sb", "st_tlsf_load_head"] +
    step_rules
  let vc = seq([
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths(rws))),
    arw(rws + [@lists.append(), @lists.length(), thm("tbv_results")]),
    g => {
      let (vs, _) = @basics.strip_exists(g.1)
      if vs.length() >= 1 {
        seq([
          @tactics.exists_tac(tm("(NIL : List[Value])")),
          @tactics.try_tac(
            @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
          ),
        ])(g)
      } else {
        @tactics.all_tac(g)
      }
    },
    arw(rws + [@lists.append(), @lists.length(), thm("tbv_results")]),
    @simp.asm_simp_tac(ths([])),
    @tactics.conv_tac(@calc_num.num_reduce_conv),
  ])
  let _ = sym_prove(
    "tlsf_find_query",
    stmt,
    [],
    Array::make(10, vc),
    afters=[after],
    rules~,
    rws~,
  )
  ignore((arw, rw))
}
