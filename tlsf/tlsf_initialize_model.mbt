// The published initial arena consists of exactly one free, last block.

///|
fn prove_tlsf_initialize_model() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let base = "val(tlsf_base((d : \{w})))"
  let lim2 = "tlsf_initialize_limit((d : \{w}),(lim : Num))"
  let _ = lemma(
    "tlsf_initialize_limit_bounds",
    "∀ d : \{w}, ∀ lim : Num, tlsf_initialize_valid(d,lim) → lim <= \{lim2} && \{lim2} <= 4294967296 && \{base}+2208 <= \{lim2} && MOD(\{lim2},65536) == 0",
    seq([
      gen,
      rw([thm("tlsf_initialize_valid")]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_page_bounds"), ["(d : \{w})"])),
      arw([]),
      strip,
      rw([thm("tlsf_initialize_limit"), @arith.max()]),
      @class.cond_cases_tac,
      arw([@arith.mult_sym(), @arith.mod_mult()]),
      @int.asm_arith_tac,
    ]),
  )
  let m = "tlsf_initialize_origin((d : \{w}))"
  let cap = "tlsf_capacity_at((lim : Num),\{m})"
  let hdr = "tlsf_initialize_header((d : \{w}),(lim : Num))"
  let hd = "tlsf_initialize_headers((d : \{w}),(lim : Num))"
  let facts = "val(d) <= 4294965088 && lim <= 4294967296 && MOD(lim,65536) == 0 && \{base}+2208 <= lim"
  let _ = lemma(
    "tlsf_initialize_header_fields",
    "∀ d : \{w}, ∀ lim : Num, \{facts} → val(\{m}) == tlsf_origin(d) && !(\{m} == word(0)) && MOD(val(\{m}),8) == 0 && 16 <= val(tlsf_size(\{hdr})) && MOD(val(tlsf_size(\{hdr})),8) == 0 && !tlsf_used(\{hdr}) && tlsf_last(\{hdr}) && val(\{m})+8+val(tlsf_size(\{hdr})) == lim",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_origin_value"), ["(d : \{w})"])),
      arw([]),
      strip,
      have(
        "MOD((lim : Num),8) == 0",
        seq([@tactics.match_mp_tac(thm("tlsf_page_aligned8")), arw([])]),
      ),
      have(
        "0 < val(\{m}) && val(\{m})+24 <= (lim : Num)",
        seq([arw([thm("tlsf_origin")]), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_capacity_fields"), ["(lim : Num)", m])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_new_top_fields"), [cap])),
      arw([]),
      strip,
      arw([thm("tlsf_initialize_header")]),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_physical",
    "∀ d : \{w}, ∀ lim : Num, \{facts} → tlsf_physical_ok(d,lim,\{m},[\{m}],\{hd})",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_header_fields"), ["(d : \{w})", "(lim : Num)"]),
      ),
      arw([]),
      strip,
      arw([
        thm("tlsf_physical_ok"),
        thm("tlsf_layout"),
        thm("tlsf_block_ok"),
        thm("tlsf_coalesced"),
        thm("tlsf_initialize_headers"),
        @lists.not_cons_nil(),
      ]),
      @meson.asm_meson_tac(ths([@arith.le_refl()])),
    ]),
  )
  let empty = "(f : Num) => (j : Num) => (NIL : List[\{w}])"
  let _ = lemma(
    "tlsf_initialize_singleton_bins",
    "∀ m : \{w}, ∀ h : \{w}, !tlsf_used(h) → tlsf_bins_match([m],(x : \{w}) => h,tlsf_push_bl(h,m,\{empty}))",
    seq([
      gen,
      @tactics.disch_tac,
      rw([
        thm("tlsf_bins_match"),
        thm("tlsf_push_bl"),
        thm("tlsf_upd"),
        thm("tlsf_level_of"),
        thm("tlsf_slot_of"),
        @lists.mem(),
      ]),
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(
            seq([
              gen,
              strip,
              subst_vars(),
              arw([
                thm("tlsf_count_cons"),
                thm("tlsf_count"),
                @lists.filter(),
                @lists.length(),
              ]),
              @tactics.conv_tac(@calc_num.num_reduce_conv),
            ]),
          ),
          solve(
            seq([
              gen,
              @tactics.repeat_tac(
                @tactics.then_tac(@class.cond_cases_tac, arw([@lists.mem()])),
              ),
              @meson.asm_meson_tac(ths([])),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
