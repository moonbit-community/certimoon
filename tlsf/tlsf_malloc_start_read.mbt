// The initial top word is either outside memory (so the guard does not load
// it), or is an aligned zero word owned by the unused startup suffix.

///|
fn malloc_start_slot() -> String {
  "word_add(tlsf_base((d : " + w32 + ")),word(1908))"
}

///|
fn malloc_start_outside() -> String {
  "word_uge(word_jushr(" +
  malloc_start_slot() +
  ",word(16)),(word(DIV((lim : Num),65536)) : " +
  w32 +
  "))"
}

///|
fn prove_tlsf_malloc_start_read() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let base = "val(tlsf_base(" + d + "))"
  let slot = malloc_start_slot()
  let address = "val(" + slot + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.repeat_tac(@tactics.strip_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = startup_lemma(
    "tlsf_malloc_start_read_bounds",
    "∀ d : " +
    w32 +
    ", ∀ lim : Num, tlsf_initialize_valid(d,lim) && !" +
    malloc_start_outside() +
    " → " +
    address +
    " == " +
    base +
    "+1908 && " +
    address +
    "+4 <= lim",
    seq([
      gen,
      strip,
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([thm("tlsf_initialize_valid")])),
      ),
      split_conjs(),
      have(
        address + " == " + base + "+1908",
        seq([
          @tactics.match_mp_tac(thm("tlsf_initialize_offset")),
          arw([]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
        ]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_initialize_old_pages"), [lim])),
      arw([]),
      strip,
      @tactics.undisch_tac(tm("!" + malloc_start_outside())),
      rw([@words.word_uge_v1(), thm("tlsf_shr16_value")]),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(inst(@arith.division(), [address, "65536"])),
      @tactics.mp_tac(inst(@arith.division(), [lim, "65536"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      arw([]),
      strip,
      have(address + " < " + lim, @int.asm_arith_tac),
      @tactics.mp_tac(inst(thm("tlsf_initialize_base_value"), [d])),
      arw([]),
      @tactics.disch_tac,
      have(
        address + " == 4*(4*DIV(val(" + d + ")+15,16)+477)",
        @int.asm_arith_tac,
      ),
      free_have(
        "MOD(" + address + ",4) == 0",
        @tactics.first_assum(th => {
          if @basics.aconv(
              @kernel.concl(th),
              tm(address + " == 4*(4*DIV(val(" + d + ")+15,16)+477)"),
            ) {
            @simp.rewrite_tac(ths([th, @arith.mod_mult()]))
          } else {
            @tactics.no_tac
          }
        }),
      ),
      @tactics.mp_tac(inst(@arith.division(), [address, "4"])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      rw([]),
      strip,
      free_have(
        "4*DIV(" + address + ",4) < 4*(16384*DIV(" + lim + ",65536))",
        @int.asm_arith_tac,
      ),
      free_have(
        "DIV(" + address + ",4) < 16384*DIV(" + lim + ",65536)",
        seq([
          @tactics.undisch_tac(
            tm("4*DIV(" + address + ",4) < 4*(16384*DIV(" + lim + ",65536))"),
          ),
          rw([@arith.lt_mult_lcancel()]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
        ]),
      ),
      @int.asm_arith_tac,
    ]),
  )
  let zero = "(word(0) : Word[8])"
  let rep = (n : String) => "REPLICATE(" + n + "," + zero + ")"
  let _ = startup_lemma(
    "tlsf_malloc_start_zero_word",
    "∀ a : Num, ∀ n : Num, ∀ k : Num, k+4 <= n → pts(a," +
    rep("n") +
    ") == star(pts(a," +
    rep("k") +
    "),star(pts(a+k,serialise_i32((word(0) : " +
    w32 +
    "))),pts(a+k+4," +
    rep("n-k-4") +
    ")))",
    seq([
      gen,
      @tactics.disch_tac,
      free_have("(k : Num) <= (n : Num)", @int.asm_arith_tac),
      free_have("4 <= (n : Num)-(k : Num)", @int.asm_arith_tac),
      g => {
        let first = block_under(
          inst(thm("tlsf_initialize_zeros_split"), [
            "(a : Num)", "(n : Num)", "(k : Num)",
          ]),
          g,
        )
        let last = block_under(
          inst(thm("tlsf_initialize_zeros_split"), [
            "(a : Num)+(k : Num)", "(n : Num)-k", "4",
          ]),
          g,
        )
        @simp.rewrite_tac(
          ths([first, last, thm("tlsf_initialize_serial_zero")]),
        )(g)
      },
    ]),
  )
  let _ = startup_lemma(
    "tlsf_malloc_start_zero_top",
    "∀ d : " +
    w32 +
    ", ∀ lim : Num, ∀ client : " +
    hprop +
    ", ∀ h : " +
    heap +
    ", tlsf_initialize_valid(d,lim) && !" +
    malloc_start_outside() +
    " → star(tlsf_initialize_zero(d,lim),client,h) → has_i32(h," +
    address +
    ",word(0))",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(inst(thm("tlsf_malloc_start_read_bounds"), [d, lim]), g),
        )(g)
      },
      have("1908+4 <= " + lim + "-" + base, @int.asm_arith_tac),
      g => {
        let focus = block_under(
          inst(thm("tlsf_malloc_start_zero_word"), [
            base,
            lim + "-" + base,
            "1908",
          ]),
          g,
        )
        ent_tac(
          [thm("tlsf_initialize_zero"), thm("has_i32"), focus] +
          g.0.to_array().map(x => x.1),
          [
            small_star([
              "pts(" + base + "," + rep("1908") + ")",
              "pts(" +
              base +
              "+1908+4," +
              rep(lim + "-" + base + "-1908-4") +
              ")",
              "(client : " + hprop + ")",
            ]),
          ],
        )(g)
      },
    ]),
  )
}
