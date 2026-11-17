///|
fn prove_tlsf_split_spatial() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let r = "tlsf_remainder((m : \{w}), (n : \{w}))"
  let rs = "tlsf_remainder_size((hd : \{ht})((m : \{w})), (n : \{w}))"
  let nh = "tlsf_split_headers((hd : \{ht}), (m : \{w}), (n : \{w}))"
  let newxs = "APPEND((ys : \{lw}), CONS((m : \{w}), CONS(\{r}, (zs : \{lw}))))"
  let newtop = "(if (zs : \{lw}) == NIL { \{r} } else { (top : \{w}) })"
  let agree = (xs : String) => {
    "∀ x : \{w}, MEM(x, \{xs}) → (hd : \{ht})(x) == (\{nh})(x)"
  }
  let cell = (a : String, v : String) => {
    "pts(\{a}, serialise_i32((\{v} : \{w})))"
  }
  let rh = "word_or(\{rs}, word_and((hd : \{ht})((m : \{w})), word(2)))"
  let nfl = "tlsf_push_fl(\{rs}, (fl : \{w}))"
  let nsb = "tlsf_push_sb(\{rs}, (sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{rs}, \{r}, (bl : \{bt}))"
  let bins = "tlsf_bins((d : \{w}), \{nfl}, \{nsb}, \{nbl})"
  let payload = "tlsf_bytes(val((m : \{w})) + 8, val((n : \{w})))"
  let ps = [
    cell("val(word_add(tlsf_base((d : " + w + ")), word(1908)))", newtop),
    "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))",
    cell("val((m : " + w + "))", "word_or((n : " + w + "), word(1))"),
    cell(
      "val(word_add((m : " + w + "), word(4)))",
      "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
    ),
    cell("val(\{r})", rh),
    cell("val(word_add(\{r}, word(4)))", "m"),
    "tlsf_bytes(val(\{r}) + 16, val(\{rs}) - 8)",
    "tlsf_regions(\{r}, (zs : \{lw}), (hd : \{ht}))",
    bins,
    payload,
  ]
  let mut spatial = "(fp : \{hprop})"
  for k = ps.length() - 1; k >= 0; k = k - 1 {
    spatial = "star(\{ps[k]}, \{spatial})"
  }
  let large = "tlsf_large((d : \{w}), (lim : Num), \{newtop}, \{newxs}, \{nh}, \{nfl}, \{nsb}, \{nbl})"
  let pure = "tlsf_physical_ok((d : \{w}), (lim : Num), \{newtop}, \{newxs}, \{nh}) && tlsf_bins_match(\{newxs}, \{nh}, \{nbl}) && (\{agree("(ys : " + lw + ")")}) && (\{agree("(zs : " + lw + ")")}) && (\{nh})(m) == word_or(n, word(1)) && (\{nh})(\{r}) == \{rh} && tlsf_size(n) == n && tlsf_size(\{rs}) == \{rs}"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let _ = lemma(
    "tlsf_split_close",
    "\{vars}, \{pure} → \{spatial} == star(\{large}, star(\{payload}, fp))",
    () => {
      seq([
        gen,
        strip,
        have(
          "tlsf_regions((word(0) : \{w}), (ys : \{lw}), \{nh}) == tlsf_regions(word(0), ys, (hd : \{ht}))",
          @tactics.accept_tac(
            @equal.sym(
              @bool.mp(
                inst(thm("tlsf_regions_cong"), [
                  "(ys : \{lw})",
                  "(word(0) : \{w})",
                  "(hd : \{ht})",
                  nh,
                ]),
                @kernel.assume_rule(tm(agree("(ys : " + lw + ")"))),
              ),
            ),
          ),
        ),
        have(
          "tlsf_regions(\{r}, (zs : \{lw}), \{nh}) == tlsf_regions(\{r}, zs, (hd : \{ht}))",
          @tactics.accept_tac(
            @equal.sym(
              @bool.mp(
                inst(thm("tlsf_regions_cong"), [
                  "(zs : \{lw})",
                  r,
                  "(hd : \{ht})",
                  nh,
                ]),
                @kernel.assume_rule(tm(agree("(zs : " + lw + ")"))),
              ),
            ),
          ),
        ),
        @tactics.mp_tac(inst(thm("tlsf_taken_fields"), ["(n : \{w})"])),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_remainder_fields"), [rs, "(hd : \{ht})((m : \{w}))"]),
        ),
        arw([]),
        strip,
        rw([@class.fun_eq_thm()]),
        gen,
        rw(
          [
            thm("tlsf_large"),
            thm("tlsf_chain"),
            thm("tlsf_regions_append"),
            thm("tlsf_regions"),
          ] +
          lift_rws(),
        ),
        arw([thm("tlsf_spare")] + lift_rws() + ac),
      ])
    },
  )
}
