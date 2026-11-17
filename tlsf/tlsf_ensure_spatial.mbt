///|
fn prove_tlsf_ensure_spatial() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (ps : Array[String]) => {
    let mut out = "(fp : \{hprop})"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    out
  }
  let pfx = "tlsf_regions((word(0) : \{w}),(ys : \{lw}),(hd : \{ht}))"
  let prev = "tlsf_end((word(0) : \{w}),(ys : \{lw}))"
  let bins = "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let nh = "(nh : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let slot = "tlsf_top_cell((d : \{w}))"
  let agree = "∀ x : \{w}, MEM(x,(ys : \{lw})) → (hd : \{ht})(x) == \{nh}(x)"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let prefix = seq([
    have(
      "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{nh}) == \{pfx}",
      @tactics.accept_tac(
        @equal.sym(
          @bool.mp(
            inst(thm("tlsf_regions_cong"), [
              "(ys : \{lw})",
              "(word(0) : \{w})",
              "(hd : \{ht})",
              nh,
            ]),
            @kernel.assume_rule(tm(agree)),
          ),
        ),
      ),
    ),
  ])
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let own = pred([
    cell(slot, "m"),
    pfx,
    cell("m", "nh(m)"),
    cell("word_add(\{m},word(4))", prev),
    "tlsf_spare(\{m},\{nh}(m))",
    bins,
  ])
  let large = "tlsf_large((d : \{w}),(lim : Num),\{m},\{xs},\{nh},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let _ = lemma(
    "tlsf_ensure_extend_close",
    "\{vars}, tlsf_physical_ok(d,lim,m,\{xs},nh) && tlsf_bins_match(\{xs},nh,bl) && (\{agree}) → \{own} == star(\{large},fp)",
    () => {
      seq([
        gen,
        strip,
        prefix,
        rw([@class.fun_eq_thm()]),
        gen,
        rw(
          [
            thm("tlsf_top_cell"),
            thm("tlsf_large"),
            thm("tlsf_chain"),
            thm("tlsf_regions_append"),
            thm("tlsf_regions"),
          ] +
          lift_rws(),
        ),
        arw(lift_rws() + ac),
      ])
    },
  )
  let nx = "APPEND((ys : \{lw}),[\{m},\{r}])"
  let own2 = pred([
    cell(slot, "r"),
    pfx,
    cell("m", "nh(m)"),
    cell("word_add(\{m},word(4))", prev),
    "tlsf_spare(\{m},\{nh}(m))",
    cell("r", "nh(r)"),
    cell("word_add(\{r},word(4))", "m"),
    "tlsf_spare(\{r},\{nh}(r))",
    bins,
  ])
  let large2 = "tlsf_large((d : \{w}),(lim : Num),\{r},\{nx},\{nh},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let _ = lemma(
    "tlsf_ensure_append_close",
    "\{vars}, ∀ r : \{w}, tlsf_physical_ok(d,lim,r,\{nx},nh) && tlsf_bins_match(\{nx},nh,bl) && (\{agree}) → \{own2} == star(\{large2},fp)",
    () => {
      seq([
        gen,
        strip,
        prefix,
        rw([@class.fun_eq_thm()]),
        gen,
        rw(
          [
            thm("tlsf_top_cell"),
            thm("tlsf_large"),
            thm("tlsf_chain"),
            thm("tlsf_regions_append"),
            thm("tlsf_regions"),
          ] +
          lift_rws(),
        ),
        arw(lift_rws() + ac),
      ])
    },
  )
}
