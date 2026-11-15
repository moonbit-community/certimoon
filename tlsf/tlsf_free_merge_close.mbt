// Fold the repaired physical chain after absorbing the removed header
// into the active block's payload.

///|
fn prove_tlsf_free_merge_close() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let star = (ps : Array[String]) => {
    let mut out = "(fp : \{hprop})"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    out
  }
  let hd = "(hd : \{ht})"
  let nh = "(nh : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},(zs : \{lw})))"
  let sm = "val(tlsf_size(\{hd}(\{m})))"
  let sr = "val(tlsf_size(\{hd}(\{r})))"
  let topcell = cell("val(tlsf_top_cell((d : " + w + ")))", "top")
  let prefix = "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})"
  let suffix = "tlsf_regions(\{m},(zs : \{lw}),\{hd})"
  let prev = cell(
    "val(word_add(\{m},word(4)))",
    "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
  )
  let mh = cell("val(\{m})", "\{nh}(\{m})")
  let bins = "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let rest = star([topcell, prefix, mh, prev, suffix, bins])
  let flat = star([
    topcell,
    prefix,
    mh,
    prev,
    "tlsf_bytes(val(\{m})+8,\{sm})",
    cell("val(\{r})", "\{hd}(\{r})"),
    cell("val(word_add(\{r},word(4)))", "m"),
    "tlsf_bytes(val(\{r})+8,\{sr})",
    suffix,
    bins,
  ])
  let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),\{m},(zs : \{lw}),\{nh},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let cond = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{nh},\{m}) && !tlsf_used(\{nh}(m)) && tlsf_bins_match(\{xs},tlsf_mark(\{nh},\{m}),(bl : \{bt})) && val(\{r}) == val(\{m})+8+\{sm} && val(word_add(\{r},word(4))) == val(r)+4 && val(tlsf_size(\{nh}(m))) == \{sm}+8+\{sr} && (∀ x : \{w}, MEM(x,APPEND((ys : \{lw}),(zs : \{lw}))) → \{nh}(x) == \{hd}(x))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let join = inst(thm("tlsf_free_join_bytes"), [
    "val(\{m})+8",
    sm,
    sr,
    "\{hd}(\{r})",
    m,
    rest,
    "(h : " + heap + ")",
  ])
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    @arith.add_assoc(),
  ]
  let _ = lemma(
    "tlsf_free_merge_close",
    "\{vars}, \{cond} → (∀ h : \{heap}, \{flat}(h) → star(\{pending},fp,h))",
    seq([
      gen,
      strip,
      seq(
        [("(ys : \{lw})", "(word(0) : \{w})"), ("(zs : \{lw})", m)].map(pair => {
          let (ls, p) = pair
          free_have(
            "tlsf_regions(\{p},\{ls},\{nh}) == tlsf_regions(\{p},\{ls},\{hd})",
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_regions_cong"), [ls, p, nh, hd]),
              ),
              @tactics.x_gen_tac(tm("(x : \{w})")),
              @tactics.disch_tac,
              @meson.asm_meson_tac(ths([@lists.mem_append()])),
            ]),
          )
        }),
      ),
      gen,
      rw([thm("tlsf_free_pending")] + lift_rws()),
      strip,
      arw([]),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      @tactics.mp_tac(join),
      arw(ac),
    ]),
  )
}
