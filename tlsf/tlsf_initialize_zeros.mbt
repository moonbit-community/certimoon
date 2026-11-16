// A zeroed startup suffix owns the empty table without enumerating its bins.

///|
fn prove_tlsf_initialize_zeros() -> Unit raise {
  let b = "Word[8]"
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let mult_suc = @tactics.prove(
    tm("∀ k : Num, ∀ n : Num, k*SUC(n) == k*n+k"),
    seq([rw([@arith.mult_suc()]), @int.arith_tac]),
  )
  let z = "(word(0) : \{b})"
  let rep = (n : String) => "REPLICATE(\{n},\{z})"
  let _ = lemma(
    "tlsf_initialize_zeros_split",
    "∀ a : Num, ∀ n : Num, ∀ k : Num, k <= n → pts(a,\{rep("n")}) == star(pts(a,\{rep("k")}),pts(a+k,\{rep("n-k")}))",
    seq([
      gen,
      @tactics.disch_tac,
      free_have("(k : Num)+(n-k) == n", @int.asm_arith_tac),
      @tactics.mp_tac(
        inst(thm("pts_split"), [
          "(a : Num)",
          rep("(k : Num)"),
          rep("(n : Num)-k"),
        ]),
      ),
      rw([@equal.gsym(thm("tlsf_replicate_add")), @lists.length_replicate()]),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_pts_nil",
    "∀ a : Num, pts(a,(NIL : List[\{b}])) == emp",
    seq([
      rw([
        @class.fun_eq_thm(),
        thm("pts"),
        thm("pts_heap"),
        thm("emp"),
        @lists.length(),
        @arith.add_clauses(),
        arith("∀ a : Num, ∀ x : Num, !(a <= x && x < a)"),
      ]),
      gen,
      @tactics.eq_tac,
      @tactics.repeat_tac(@tactics.strip_tac),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_zero_segments",
    "∀ n : Num, ∀ a : Num, ∀ k : Num, tlsf_istar((i : Num) => pts(a+k*i,\{rep("k")}),(n : Num)) == pts(a,\{rep("k*n")})",
    seq([
      @nums.induct_tac,
      rw([
        thm("tlsf_istar"),
        @arith.mult_clauses(),
        @arith.add_clauses(),
        @lists.replicate(),
        thm("tlsf_initialize_pts_nil"),
      ]),
      gen,
      free_have("(k : Num)+k*(n : Num) == k*n+k", @int.arith_tac),
      arw([]),
      @tactics.mp_tac(
        inst(thm("pts_split"), [
          "(a : Num)",
          rep("(k : Num)*n"),
          rep("(k : Num)"),
        ]),
      ),
      rw([
        @equal.gsym(thm("tlsf_replicate_add")),
        @lists.length_replicate(),
        mult_suc,
      ]),
      @tactics.disch_then(th => @tactics.mp_tac(th)),
      rw([@class.eta_ax(), @arith.add_sym()]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_serial_zero",
    "serialise_i32((word(0) : \{w})) == \{rep("4")}",
    seq([
      rw([
        @wasm.thm("serialise_i32"),
        @words.val_word_0(),
        thm("tlsf_le_zero_bytes"),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_empty_sync",
    "∀ n : Num, tlsf_sync((word(0) : \{w}),n,(i : Num) => F)",
    seq([rw([thm("tlsf_sync"), @words.bit_word_0()])]),
  )
  let base = "tlsf_base((d : \{w}))"
  let _ = lemma(
    "tlsf_initialize_offset",
    "∀ d : \{w}, ∀ k : Num, val(d) <= 4294965088 && k <= 2176 → val(word_add(\{base},word(k))) == val(\{base})+k",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_base_bounds"), ["(d : \{w})"])),
      arw([]),
      strip,
      @tactics.match_mp_tac(thm("val_add_small")),
      @int.asm_arith_tac,
    ]),
  )
  let slot = "word_add(word_add(word_add(word_add(\{base},word(4)),word_mul((word((f : Num)) : \{w}),word(68))),word(4)),word_jshl((word((j : Num)) : \{w}),word(2)))"
  let word : @tactics.Tactic = g => {
    @tactics.accept_tac(@words.word_rule(g.1))(g)
  }
  let _ = lemma(
    "tlsf_initialize_slot_word",
    "∀ d : \{w}, ∀ f : Num, ∀ j : Num, \{slot} == word_add(\{base},word(8+68*f+4*j))",
    seq([
      gen,
      rw([
        @words.word_jshl(),
        @words.word_shl_word(),
        @words.val_word(),
        @words.dimindex_32(),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      word,
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_slot_address",
    "∀ d : \{w}, ∀ f : Num, ∀ j : Num, val(d) <= 4294965088 && f < 28 && j < 16 → val(\{slot}) == val(\{base})+8+68*f+4*j",
    seq([
      gen,
      strip,
      rw([thm("tlsf_initialize_slot_word")]),
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_offset"), [
          "(d : \{w})",
          "8+68*(f : Num)+4*(j : Num)",
        ]),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let empty = "(NIL : List[\{w}])"
  let _ = lemma(
    "tlsf_initialize_empty_slots",
    "∀ d : \{w}, ∀ f : Num, val(d) <= 4294965088 && f < 28 → tlsf_istar((j : Num) => tlsf_slot_item(d,word(f),j,\{empty}),16) == pts(val(\{base})+8+68*f,\{rep("64")})",
    seq([
      gen,
      strip,
      free_have(
        "tlsf_istar((j : Num) => tlsf_slot_item((d : \{w}),word((f : Num)),j,\{empty}),16) == tlsf_istar((j : Num) => pts(val(\{base})+8+68*f+4*j,\{rep("4")}),16)",
        seq([
          @tactics.match_mp_tac(thm("tlsf_istar_cong")),
          gen,
          @tactics.disch_tac,
          rw([
            thm("tlsf_slot_item"),
            thm("tlsf_bin"),
            thm("tlsf_hd"),
            thm("tlsf_dll"),
            @class.eta_ax(),
            thm("star_emp_hr"),
            thm("tlsf_initialize_serial_zero"),
            @equal.gsym(thm("tlsf_base")),
          ]),
          @tactics.mp_tac(
            inst(thm("tlsf_initialize_slot_address"), [
              "(d : \{w})",
              "(f : Num)",
              "(i : Num)",
            ]),
          ),
          arw([]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      arw([]),
      rw([@equal.gsym(@arith.add_assoc()), thm("tlsf_initialize_zero_segments")]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  let row = "word_add(word_add(\{base},word(4)),word_mul((word((f : Num)) : \{w}),word(68)))"
  let _ = lemma(
    "tlsf_initialize_row_address",
    "∀ d : \{w}, ∀ f : Num, val(d) <= 4294965088 && f < 28 → val(\{row}) == val(\{base})+4+68*f",
    seq([
      gen,
      strip,
      free_have("\{row} == word_add(\{base},word(4+68*f))", word),
      arw([]),
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_offset"), ["(d : \{w})", "4+68*(f : Num)"]),
      ),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_empty_level",
    "∀ d : \{w}, ∀ f : Num, val(d) <= 4294965088 && f < 28 → tlsf_level(d,f,word(0),(j : Num) => \{empty}) == pts(val(\{base})+4+68*f,\{rep("68")})",
    seq([
      gen,
      strip,
      free_have(
        "val(\{row}) == val(\{base})+4+68*f",
        seq([@tactics.match_mp_tac(thm("tlsf_initialize_row_address")), arw([])]),
      ),
      free_have(
        "tlsf_istar((j : Num) => tlsf_slot_item((d : \{w}),word((f : Num)),j,\{empty}),16) == pts(val(\{base})+8+68*f,\{rep("64")})",
        seq([@tactics.match_mp_tac(thm("tlsf_initialize_empty_slots")), arw([])]),
      ),
      rw([
        thm("tlsf_level"),
        thm("tlsf_initialize_empty_sync"),
        thm("tlsf_initialize_serial_zero"),
        @equal.gsym(thm("tlsf_base")),
      ]),
      arw([]),
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_zeros_split"), [
          "val(\{base})+4+68*(f : Num)",
          "68",
          "4",
        ]),
      ),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      rw([
        arith("∀ a : Num, ∀ f : Num, a+4+68*f+4 == a+8+68*f"),
        @class.eta_ax(),
      ]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_empty_bins",
    "∀ d : \{w}, val(d) <= 4294965088 → tlsf_bins(d,word(0),(f : Num) => word(0),(f : Num) => (j : Num) => \{empty}) == pts(val(\{base}),\{rep("1908")})",
    seq([
      gen,
      @tactics.disch_tac,
      free_have(
        "tlsf_istar((f : Num) => tlsf_level((d : \{w}),f,word(0),(j : Num) => \{empty}),28) == tlsf_istar((f : Num) => pts(val(\{base})+4+68*f,\{rep("68")}),28)",
        seq([
          @tactics.match_mp_tac(thm("tlsf_istar_cong")),
          gen,
          @tactics.disch_tac,
          beta_goal(),
          @tactics.match_mp_tac(thm("tlsf_initialize_empty_level")),
          arw([]),
        ]),
      ),
      rw([
        thm("tlsf_bins"),
        thm("tlsf_initialize_empty_sync"),
        thm("tlsf_initialize_serial_zero"),
        @equal.gsym(thm("tlsf_base")),
      ]),
      arw([thm("tlsf_initialize_zero_segments")]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @tactics.mp_tac(
        inst(thm("tlsf_initialize_zeros_split"), ["val(\{base})", "1908", "4"]),
      ),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      rw([@class.eta_ax()]),
      @meson.meson_tac(ths([])),
    ]),
  )
}
