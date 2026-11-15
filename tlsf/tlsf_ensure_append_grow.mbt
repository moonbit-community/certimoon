///|
fn prove_tlsf_ensure_append_grow() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let h = "\{hd}(\{m})"
  let lim2 = "(lim : Num)+(delta : Num)"
  let r = "(word((lim : Num)) : \{w})"
  let cap = "tlsf_capacity_at(\{lim2},\{r})"
  let zero = "pts((lim : Num),REPLICATE((delta : Num),(word(0) : Word[8])))"
  let large = "tlsf_large((d : \{w}),(lim : Num),\{m},\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let ps = [
    cell("tlsf_top_cell((d : " + w + "))", "m"),
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
    cell("m", h),
    cell(
      "word_add(\{m},word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
  ]
  let mut frame = "(fp : \{hprop})"
  for k = ps.length() - 1; k >= 0; k = k - 1 {
    frame = "star(\{ps[k]},\{frame})"
  }
  let head = "star(\{cell(r,"word(0)")},star(\{cell("word_add(\{r},word(4))","word(0)")},tlsf_bytes(val(\{r})+8,val(\{cap}))))"
  let target = "star(\{head},\{frame},(heap0 : \{heap}))"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ delta : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd})"
  let cond = "\{old} && tlsf_used(\{h}) && 24 <= (delta : Num) && \{lim2} <= 4294967296"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let _ = lemma(
    "tlsf_ensure_append_grow",
    "\{vars}, \{cond} → (∀ heap0 : \{heap}, star(\{large},star(\{zero},fp),heap0) → \{target})",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_ensure_top_facts"), [
          "(ys : \{lw})",
          "(d : \{w})",
          "(lim : Num)",
          m,
          hd,
        ]),
      ),
      arw([]),
      strip,
      have("(lim : Num) < 4294967296", @int.asm_arith_tac),
      have(
        "val(\{r}) == (lim : Num)",
        seq([
          rw([@words.val_word(), @words.dimindex_32()]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @simp.asm_simp_tac(ths([@arith.mod_lt()])),
        ]),
      ),
      have("0 < (lim : Num)", @int.asm_arith_tac),
      have(
        "val(word_add(\{r},word(4))) == (lim : Num)+4",
        seq([
          @tactics.mp_tac(inst(thm("val_add_small"), [r, "4"])),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_capacity_value"), [lim2, r])),
      arw([]),
      have("(lim : Num)+24 <= \{lim2}", @int.asm_arith_tac),
      arw([]),
      @tactics.disch_tac,
      have("val(\{cap}) == (delta : Num)-8", @int.asm_arith_tac),
      gen,
      rw(
        [
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("tlsf_regions_append"),
          thm("tlsf_regions"),
          thm("tlsf_spare"),
        ] +
        lift_rws(),
      ),
      strip,
      have(
        "star(\{zero},\{frame},(heap0 : \{heap}))",
        seq([
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "star" {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          arw([thm("tlsf_top_cell")] + lift_rws() + ac),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_new_memory_frame"), [
          "(lim : Num)",
          "(delta : Num)",
          frame,
          "(heap0 : \{heap})",
        ]),
      ),
      arw([]),
      have("8 <= (delta : Num)", @int.asm_arith_tac),
      arw([arith("(lim : Num)+(delta : Num)-lim-8 == delta-8")]),
    ]),
  )
}
