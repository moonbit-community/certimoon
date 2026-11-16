// Carve the startup zero suffix into the empty table, untouched page table,
// header/link words, and the payload of the first block.

///|
fn prove_tlsf_initialize_ready() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let base = "val(tlsf_base(\{d}))"
  let m = "tlsf_initialize_origin(\{d})"
  let hdr = "tlsf_initialize_header(\{d},\{lim})"
  let facts = "val(d) <= 4294965088 && lim <= 4294967296 && MOD(lim,65536) == 0 && \{base}+2208 <= lim"
  let normal = [
    @equal.gsym(@arith.add_assoc()),
    arith("∀ n : Num, ∀ a : Num, ∀ b : Num, n-a-b == n-(a+b)"),
    @arith.add_clauses(),
  ]
  let cuts = [
    (0, 1908),
    (1908, 4),
    (1912, 264),
    (2176, 4),
    (2180, 4),
    (2184, 4),
    (2188, 4),
  ]
  let rules = cuts.map(c => {
    let (start, len) = c
    @equal.conv_rule(
      @calc_num.num_reduce_conv,
      @simp.rewrite_rule(ths(normal))(
        @bool.undisch(
          inst(thm("tlsf_initialize_zeros_split"), [
            "\{base}+\{start}",
            "\{lim}-(\{base}+\{start})",
            len.to_string(),
          ]),
        ),
      ),
    )
  })
  let payload = "REPLICATE(\{lim}-(\{base}+2192),(word(0) : Word[8]))"
  let _ = lemma(
    "tlsf_initialize_zero_ready",
    "∀ d : \{w}, ∀ lim : Num, ∀ fp : \{rty}, ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{facts} → ms == lim && star(tlsf_initialize_zero(d,lim),fp(gs,ms),h) → tlsf_initialize_work(d,lim,word(0),F,word(0),fp,gs,ms,h)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_header_fields"), [d, lim])),
      arw([]),
      strip,
      free_have("val(\{m}) == \{base}+2176", arw([thm("tlsf_origin")])),
      free_have(
        "val(tlsf_size(\{hdr}))-8 == \{lim}-(\{base}+2192)",
        @int.asm_arith_tac,
      ),
      seq(
        [4, 8, 12].map(k => {
          free_have(
            "val(word_add(\{m},word(\{k}))) == \{base}+\{2176+k}",
            seq([
              @tactics.mp_tac(inst(thm("val_add_small"), [m, k.to_string()])),
              arw([]),
              @int.asm_arith_tac,
            ]),
          )
        }),
      ),
      seq(
        rules.map(rule => {
          free_have(show(@kernel.hyp(rule).to_array()[0]), @int.asm_arith_tac)
        }),
      ),
      free_have(
        "tlsf_bins(\{d},word(0),(f : Num) => word(0),(f : Num) => (j : Num) => (NIL : List[\{w}])) == pts(\{base},REPLICATE(1908,(word(0) : Word[8])))",
        seq([@tactics.match_mp_tac(thm("tlsf_initialize_empty_bins")), arw([])]),
      ),
      free_have(
        "val(tlsf_top_cell(\{d})) == \{base}+1908",
        seq([
          rw([thm("tlsf_top_cell")]),
          @tactics.match_mp_tac(thm("tlsf_initialize_offset")),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.disch_tac,
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      rw(
        [
          thm("tlsf_initialize_zero"),
          thm("tlsf_initialize_work"),
          thm("tlsf_spare"),
          thm("tlsf_bytes"),
          thm("tlsf_initialize_serial_zero"),
        ] +
        lift_rws(),
      ),
      arw([]),
      rw(rules + normal + lift_rws() + [thm("tlsf_origin")]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.exists_tac(tm(payload)),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(
        [
          @lists.length_replicate(),
          thm("star_assoc"),
          thm("star_comm"),
          thm("star_left_comm"),
        ] +
        normal,
      ),
    ]),
  )
}
