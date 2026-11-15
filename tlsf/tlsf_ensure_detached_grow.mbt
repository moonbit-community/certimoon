///|
fn prove_tlsf_ensure_detached_grow() -> Unit raise {
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
  let sz = "val(tlsf_size(\{h}))"
  let lim2 = "(lim : Num)+(delta : Num)"
  let cap = "tlsf_capacity_at(\{lim2},\{m})"
  let zero = "pts((lim : Num),REPLICATE((delta : Num),(word(0) : Word[8])))"
  let det = "tlsf_detached((d : \{w}),(lim : Num),\{m},(ys : \{lw}),\{m},NIL,\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
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
  let payload = "tlsf_bytes(val(\{m})+8,\{sz})"
  let target = "star(tlsf_bytes(val(\{m})+8,val(\{cap})),\{frame},(heap0 : \{heap}))"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ delta : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let cond = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd}) && !tlsf_used(\{h}) && \{lim2} <= 4294967296"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let _ = lemma(
    "tlsf_ensure_detached_grow",
    "\{vars}, \{cond} → (∀ heap0 : \{heap}, star(\{det},star(\{zero},fp),heap0) → \{target})",
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
      have("val(\{m})+24 <= \{lim2}", @int.asm_arith_tac),
      @tactics.mp_tac(inst(thm("tlsf_capacity_value"), [lim2, m])),
      arw([]),
      @tactics.disch_tac,
      have("val(\{cap}) == \{sz}+(delta : Num)", @int.asm_arith_tac),
      have(
        "((lim : Num)+(delta : Num))-val(\{m})-8 == \{sz}+(delta : Num)",
        @int.asm_arith_tac,
      ),
      gen,
      rw([thm("tlsf_detached"), thm("tlsf_regions")] + lift_rws()),
      strip,
      have(
        "star(\{payload},star(\{zero},\{frame}),(heap0 : \{heap}))",
        seq([
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "star" {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          arw([thm("tlsf_top_cell")] + ac),
        ]),
      ),
      arw([]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_grown_bytes_frame"), [
          "val(\{m})+8",
          sz,
          "(delta : Num)",
          frame,
          "(heap0 : \{heap})",
        ]),
      ),
      @tactics.undisch_tac(
        tm("star(\{payload},star(\{zero},\{frame}),(heap0 : \{heap}))"),
      ),
      arw([]),
    ]),
  )
}
