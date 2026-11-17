// Initialized TLSF memories, in physical address order. A header map is
// shared by the geometric model and the bin correspondence, while the
// spatial predicates own different fields: physical headers and free
// payload tails here, free-list links in tlsf_bins.mbt. Used payloads
// remain available to the client or the later small-page invariant.
//
// Limits and endpoints are Nums, including a memory32 endpoint of 2^32.
// Coalescing is kept separate from geometry for intermediate free states.
// Compiled search and split preservation are proved in tlsf_find_*.mbt
// and tlsf_split_*.mbt.

// Physical blocks and the relation between their headers and the bins.

///|
fn prove_tlsf_physical() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  def("tlsf_size", "tlsf_size((hd : \{w})) == word_and(hd, word(4294967292))")
  def(
    "tlsf_used",
    "tlsf_used((hd : \{w})) == !(word_and(hd, word(1)) == word(0))",
  )
  def(
    "tlsf_last",
    "tlsf_last((hd : \{w})) == !(word_and(hd, word(2)) == word(0))",
  )
  def(
    "tlsf_level_of",
    "tlsf_level_of((hd : \{w})) == val((word_sub(word(27), word(word_clz(tlsf_size(hd)))) : \{w}))",
  )
  def(
    "tlsf_slot_of",
    "tlsf_slot_of((hd : \{w})) == val(word_and(word_jushr(tlsf_size(hd), word_sub(word(27), word(word_clz(tlsf_size(hd))))), word(15)))",
  )
  let class_rws = [thm("tlsf_level_of"), thm("tlsf_slot_of")]
  let _ = lemma(
    "tlsf_header_class_bounds",
    "∀ hd : \{w}, 16 <= val(tlsf_size(hd)) → tlsf_level_of(hd) < 28 && tlsf_slot_of(hd) < 16",
    () => {
      seq([gen, rw(class_rws), @meson.meson_tac(ths([thm("tlsf_code_bounds")]))])
    },
  )
  let _ = lemma(
    "tlsf_header_class",
    "∀ hd : \{w}, tlsf_level_of(hd) == val(word_sub(tlsf_fli(tlsf_size(hd)), word(4))) && tlsf_slot_of(hd) == val(tlsf_sli(tlsf_size(hd), tlsf_fli(tlsf_size(hd))))",
    () => rw(class_rws + [thm("tlsf_code_fli"), thm("tlsf_code_sli")]),
  )
  // The endpoint is a Num, including 2^32, rather than a wrapping word.
  def(
    "tlsf_block_ok",
    "tlsf_block_ok((a : Num), (lim : Num), (m : \{w}), (hd : \{ht})) == (val(m) == a && !(m == word(0)) && MOD(a, 8) == 0 && 16 <= val(tlsf_size(hd(m))) && MOD(val(tlsf_size(hd(m))), 8) == 0 && a + 8 + val(tlsf_size(hd(m))) <= lim)",
  )
  def(
    "tlsf_layout",
    "tlsf_layout((p : \{w}), (a : Num), (lim : Num), (top : \{w}), (NIL : \{lw}), (hd : \{ht})) == (a == lim && p == top) && tlsf_layout(p, a, lim, top, CONS((m : \{w}), xs), hd) == (tlsf_block_ok(a, lim, m, hd) && (tlsf_last(hd(m)) == (xs == NIL)) && tlsf_layout(m, a + 8 + val(tlsf_size(hd(m))), lim, top, xs, hd))",
  )
  let layout = thm("tlsf_layout")
  let block = thm("tlsf_block_ok")
  let _ = lemma(
    "tlsf_block_field_address",
    "∀ a : Num, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ k : Num, tlsf_block_ok(a, lim, m, hd) && lim <= 4294967296 && k <= 16 → val(word_add(m, word(k))) == val(m) + k",
    () => {
      seq([
        gen,
        rw([block]),
        strip,
        @tactics.match_mp_tac(thm("val_add_small")),
        @int.asm_arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_block_spare_end",
    "∀ a : Num, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}, tlsf_block_ok(a, lim, m, hd) → val(m) + 16 + (val(tlsf_size(hd(m))) - 8) == val(m) + 8 + val(tlsf_size(hd(m)))",
    () => seq([gen, rw([block]), strip, @int.asm_arith_tac]),
  )
  let lower = lemma(
    "tlsf_layout_lower",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_layout(p, a, lim, top, xs, hd) && MEM(m, xs) → a <= val(m)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([layout, @lists.mem()]),
        gen,
        strip,
        arw([@lists.mem()]),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.mp_tac(
                  @kernel.assume_rule(
                    tm(
                      "tlsf_block_ok((a : Num), (lim : Num), (h : \{w}), (hd : \{ht}))",
                    ),
                  ),
                ),
                rw([block]),
                strip,
                @int.asm_arith_tac,
              ]),
            ),
            solve(
              seq([
                have(
                  "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w})))) <= val((m : \{w}))",
                  seq([
                    @tactics.first_x_assum(th => {
                      @tactics.match_mp_tac(
                        inst(th, [
                          "(h : \{w})",
                          "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                          "(lim : Num)",
                          "(top : \{w})",
                          "(hd : \{ht})",
                          "(m : \{w})",
                        ]),
                      )
                    }),
                    arw([]),
                  ]),
                ),
                @int.asm_arith_tac,
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let members = lemma(
    "tlsf_layout_members",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_layout(p, a, lim, top, xs, hd) && MEM(m, xs) → tlsf_block_ok(val(m), lim, m, hd)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([layout, @lists.mem()]),
        gen,
        strip,
        arw([@lists.mem()]),
        @tactics.first(
          @list.List([
            solve(
              seq([
                @tactics.mp_tac(
                  @kernel.assume_rule(
                    tm(
                      "tlsf_block_ok((a : Num), (lim : Num), (h : \{w}), (hd : \{ht}))",
                    ),
                  ),
                ),
                rw([block]),
                strip,
                arw([block]),
              ]),
            ),
            solve(
              seq([
                @tactics.first_x_assum(th => {
                  @tactics.match_mp_tac(
                    inst(th, [
                      "(h : \{w})",
                      "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                      "(lim : Num)",
                      "(top : \{w})",
                      "(hd : \{ht})",
                      "(m : \{w})",
                    ]),
                  )
                }),
                arw([]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_layout_order",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_layout(p, a, lim, top, xs, hd) → PAIRWISE((m : \{w}) => (n : \{w}) => val(m) + 8 + val(tlsf_size(hd(m))) <= val(n), xs)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([layout, @lists.pairwise()]),
        gen,
        strip,
        have(
          "val((h : \{w})) == (a : Num)",
          seq([
            @tactics.mp_tac(
              @kernel.assume_rule(
                tm(
                  "tlsf_block_ok((a : Num), (lim : Num), (h : \{w}), (hd : \{ht}))",
                ),
              ),
            ),
            rw([block]),
            strip,
            arw([]),
          ]),
        ),
        arw([@lists.all(), @lists.pairwise()]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              rw([@equal.gsym(@lists.all_mem())]),
              gen,
              @tactics.disch_tac,
              @tactics.match_mp_tac(
                inst(lower, [
                  "(t : \{lw})",
                  "(h : \{w})",
                  "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                  "(lim : Num)",
                  "(top : \{w})",
                  "(hd : \{ht})",
                  "(x : \{w})",
                ]),
              ),
              arw([]),
            ]),
            seq([
              @tactics.first_x_assum(th => {
                @tactics.match_mp_tac(
                  inst(th, [
                    "(h : \{w})",
                    "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))",
                    "(lim : Num)",
                    "(top : \{w})",
                    "(hd : \{ht})",
                  ]),
                )
              }),
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_layout_distinct",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, tlsf_layout(p, a, lim, top, xs, hd) → PAIRWISE((m : \{w}) => (n : \{w}) => !(m == n), xs)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.match_mp_tac(@lists.pairwise_implies()),
        @tactics.exists_tac(
          tm(
            "(m : \{w}) => (n : \{w}) => val(m) + 8 + val(tlsf_size((hd : \{ht})(m))) <= val(n)",
          ),
        ),
        beta_goal(),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_layout_order"), [
                  "(xs : \{lw})",
                  "(p : \{w})",
                  "(a : Num)",
                  "(lim : Num)",
                  "(top : \{w})",
                  "(hd : \{ht})",
                ]),
              ),
              arw([]),
            ]),
            seq([
              gen,
              strip,
              @class.asm_cases_tac(tm("(x : \{w}) == y")),
              subst_vars(),
              arw([]),
              @int.asm_arith_tac,
            ]),
          ]),
        ),
      ])
    },
  )
  // Count actual list occurrences, so two copies in the same bin are
  // excluded as well as occurrences in different size classes.
  def(
    "tlsf_count",
    "tlsf_count((m : \{w}), (xs : \{lw})) == LENGTH(FILTER((x : \{w}) => x == m, xs))",
  )
  let count_member = lemma(
    "tlsf_count_member",
    "∀ m : \{w}, ∀ xs : \{lw}, MEM(m, xs) == (0 < tlsf_count(m, xs))",
    () => rw([thm("tlsf_count"), thm("mem_count")]),
  )
  let count_zero = lemma(
    "tlsf_count_zero",
    "∀ m : \{w}, ∀ xs : \{lw}, (tlsf_count(m, xs) == 0) == !MEM(m, xs)",
    () => seq([gen, rw([thm("tlsf_count"), thm("mem_count")]), @int.arith_tac]),
  )
  def(
    "tlsf_bins_match",
    "tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt})) == ((∀ m : \{w}, MEM(m, xs) && !tlsf_used(hd(m)) → tlsf_count(m, bl(tlsf_level_of(hd(m)))(tlsf_slot_of(hd(m)))) == 1) && (∀ f : Num, ∀ j : Num, ∀ m : \{w}, f < 28 && j < 16 && MEM(m, bl(f)(j)) → MEM(m, xs) && !tlsf_used(hd(m)) && tlsf_level_of(hd(m)) == f && tlsf_slot_of(hd(m)) == j))",
  )
  let exact = lemma(
    "tlsf_bins_match_exact",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, ∀ f : Num, ∀ j : Num, tlsf_bins_match(xs, hd, bl) && f < 28 && j < 16 → tlsf_count(m, bl(f)(j)) == (if MEM(m, xs) && !tlsf_used(hd(m)) && tlsf_level_of(hd(m)) == f && tlsf_slot_of(hd(m)) == j { 1 } else { 0 })",
    () => {
      seq([
        gen,
        rw([thm("tlsf_bins_match")]),
        strip,
        @class.cond_cases_tac,
        arw([]),
        @tactics.first(
          @list.List([
            solve(@meson.asm_meson_tac(ths([]))),
            solve(seq([rw([count_zero]), @meson.asm_meson_tac(ths([]))])),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_bins_match_member",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, ∀ f : Num, ∀ j : Num, tlsf_bins_match(xs, hd, bl) && f < 28 && j < 16 → (MEM(m, bl(f)(j)) == (MEM(m, xs) && !tlsf_used(hd(m)) && tlsf_level_of(hd(m)) == f && tlsf_slot_of(hd(m)) == j))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(exact, [
            "(xs : \{lw})",
            "(hd : \{ht})",
            "(bl : \{bt})",
            "(m : \{w})",
            "(f : Num)",
            "(j : Num)",
          ]),
        ),
        arw([]),
        @class.cond_cases_tac,
        arw([count_member]),
        @int.arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_bins_match_unique",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ m : \{w}, ∀ f : Num, ∀ j : Num, ∀ g : Num, ∀ k : Num, tlsf_bins_match(xs, hd, bl) && f < 28 && j < 16 && g < 28 && k < 16 && MEM(m, bl(f)(j)) && MEM(m, bl(g)(k)) → f == g && j == k && tlsf_count(m, bl(f)(j)) == 1",
    () => {
      seq([
        gen,
        strip,
        have(
          "MEM((m : \{w}), (xs : \{lw})) && !tlsf_used((hd : \{ht})(m)) && tlsf_level_of(hd(m)) == (f : Num) && tlsf_slot_of(hd(m)) == (j : Num)",
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_bins_match_member"), [
                "(xs : \{lw})",
                "(hd : \{ht})",
                "(bl : \{bt})",
                "(m : \{w})",
                "(f : Num)",
                "(j : Num)",
              ]),
            ),
            arw([]),
          ]),
        ),
        have(
          "MEM((m : \{w}), (xs : \{lw})) && !tlsf_used((hd : \{ht})(m)) && tlsf_level_of(hd(m)) == (g : Num) && tlsf_slot_of(hd(m)) == (k : Num)",
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_bins_match_member"), [
                "(xs : \{lw})",
                "(hd : \{ht})",
                "(bl : \{bt})",
                "(m : \{w})",
                "(g : Num)",
                "(k : Num)",
              ]),
            ),
            arw([]),
          ]),
        ),
        @tactics.mp_tac(
          inst(exact, [
            "(xs : \{lw})",
            "(hd : \{ht})",
            "(bl : \{bt})",
            "(m : \{w})",
            "(f : Num)",
            "(j : Num)",
          ]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
  // Header ownership is disjoint from the free-list links. Free payload
  // bytes after the links belong to the allocator; used payloads do not.
  def(
    "tlsf_bytes",
    "tlsf_bytes((a : Num), (n : Num)) == ((h : \{heap}) => ∃ bs : List[Word[8]], LENGTH(bs) == n && pts(a, bs, h))",
  )
  def(
    "tlsf_spare",
    "tlsf_spare((m : \{w}), (hd : \{w})) == (if tlsf_used(hd) { emp } else { tlsf_bytes(val(m) + 16, val(tlsf_size(hd)) - 8) })",
  )
  let cell = (a : String, v : String) => {
    "pts(\{a}, serialise_i32((\{v} : \{w})))"
  }
  def(
    "tlsf_regions",
    "tlsf_regions((p : \{w}), (NIL : \{lw}), (hd : \{ht})) == emp && tlsf_regions(p, CONS((m : \{w}), xs), hd) == star(\{cell("val(m)", "hd(m)")}, star(\{cell("val(word_add(m, word(4)))", "p")}, star(tlsf_spare(m, hd(m)), tlsf_regions(m, xs, hd))))",
  )
  def(
    "tlsf_base",
    "tlsf_base((d : \{w})) == word_and(word_add(d, word(15)), word(4294967280))",
  )
  def("tlsf_origin", "tlsf_origin((d : \{w})) == val(tlsf_base(d)) + 2176")
  // Coalescing is separate from geometry so helper specs can describe
  // the intermediate state before free has merged its neighbours.
  def(
    "tlsf_coalesced",
    "tlsf_coalesced((NIL : \{lw}), (hd : \{ht})) == T && tlsf_coalesced(CONS((m : \{w}), xs), hd) == ((xs == NIL || tlsf_used(hd(m)) || tlsf_used(hd(HD(xs)))) && tlsf_coalesced(xs, hd))",
  )
  def(
    "tlsf_physical_ok",
    "tlsf_physical_ok((d : \{w}), (ms : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht})) == (val(d) <= 4294965088 && ms <= 4294967296 && MOD(ms, 65536) == 0 && !(xs == NIL) && tlsf_layout(word(0), tlsf_origin(d), ms, top, xs, hd) && tlsf_coalesced(xs, hd))",
  )
  def(
    "tlsf_chain",
    "tlsf_chain((d : \{w}), (ms : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht})) == ((h : \{heap}) => tlsf_physical_ok(d, ms, top, xs, hd) && star(\{cell("val(word_add(tlsf_base(d), word(1908)))", "top")}, tlsf_regions(word(0), xs, hd), h))",
  )
  def(
    "tlsf_large",
    "tlsf_large((d : \{w}), (ms : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})) == ((h : \{heap}) => tlsf_bins_match(xs, hd, bl) && star(tlsf_chain(d, ms, top, xs, hd), tlsf_bins(d, fl, sb, bl), h))",
  )
  let _ = lemma(
    "tlsf_large_layout",
    "∀ d : \{w}, ∀ ms : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, tlsf_large(d, ms, top, xs, hd, fl, sb, bl, h) → tlsf_layout(word(0), tlsf_origin(d), ms, top, xs, hd)",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("tlsf_physical_ok"),
          thm("star_pure_hl"),
        ]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_large_free_exact",
    "∀ d : \{w}, ∀ ms : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, ∀ m : \{w}, ∀ f : Num, ∀ j : Num, tlsf_large(d, ms, top, xs, hd, fl, sb, bl, h) && f < 28 && j < 16 → tlsf_count(m, bl(f)(j)) == (if MEM(m, xs) && !tlsf_used(hd(m)) && tlsf_level_of(hd(m)) == f && tlsf_slot_of(hd(m)) == j { 1 } else { 0 })",
    () => seq([gen, rw([thm("tlsf_large")]), @meson.meson_tac(ths([exact]))]),
  )
  let _ = lemma(
    "tlsf_large_order",
    "∀ d : \{w}, ∀ ms : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, tlsf_large(d, ms, top, xs, hd, fl, sb, bl, h) → PAIRWISE((m : \{w}) => (n : \{w}) => val(m) + 8 + val(tlsf_size(hd(m))) <= val(n), xs)",
    () => {
      @meson.meson_tac(
        ths([thm("tlsf_large_layout"), thm("tlsf_layout_order")]),
      )
    },
  )
  let _ = lemma(
    "tlsf_large_free_once",
    "∀ d : \{w}, ∀ ms : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ h : \{heap}, ∀ m : \{w}, tlsf_large(d, ms, top, xs, hd, fl, sb, bl, h) && MEM(m, xs) && !tlsf_used(hd(m)) → tlsf_level_of(hd(m)) < 28 && tlsf_slot_of(hd(m)) < 16 && tlsf_count(m, bl(tlsf_level_of(hd(m)))(tlsf_slot_of(hd(m)))) == 1",
    () => {
      seq([
        gen,
        strip,
        have(
          "tlsf_layout(word(0), tlsf_origin((d : \{w})), (ms : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}))",
          @meson.asm_meson_tac(ths([thm("tlsf_large_layout")])),
        ),
        have(
          "tlsf_block_ok(val((m : \{w})), (ms : Num), m, (hd : \{ht}))",
          @meson.asm_meson_tac(ths([members])),
        ),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(
            ths([block, thm("tlsf_large"), thm("tlsf_bins_match")]),
          ),
        ),
        @meson.asm_meson_tac(ths([thm("tlsf_header_class_bounds")])),
      ])
    },
  )
}
