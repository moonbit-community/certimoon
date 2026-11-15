///|
fn prove_tlsf_ensure_saved() -> Unit raise {
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
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let large = "tlsf_large((d : \{w}),(lim : Num),\{m},\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let ps = [
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
    cell(
      "word_add(\{m},word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    "tlsf_spare(\{m},\{hd}(m))",
    "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
  ]
  let mut frame = "(fp : \{rty})((gs : List[Value]),(lim : Num))"
  for k = ps.length() - 1; k >= 0; k = k - 1 {
    frame = "star(\{ps[k]},\{frame})"
  }
  let args = "(d : \{w}),(lim : Num),(ys : \{lw}),\{m},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(fp : \{rty})"
  def(
    "tlsf_ensure_frame",
    "tlsf_ensure_frame(\{args}) == ((gs : List[Value]) => (ms : Num) => \{frame})",
  )
  let ro = "tlsf_ensure_ro((d : \{w}),\{m},\{hd}(m),(lim : Num),(before : \{heap}),tlsf_ensure_frame(\{args}))"
  let saved = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && h == (before : \{heap}) && star(\{large},(fp : \{rty})(gs,lim),h)"
  def(
    "tlsf_ensure_saved",
    "tlsf_ensure_saved(\{args},(before : \{heap})) == (\{saved})",
  )
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}, ∀ before : \{heap}"
  let cond = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd}) && tlsf_bins_match(\{xs},\{hd},(bl : \{bt}))"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let eq = lemma(
    "tlsf_ensure_ro_saved",
    "\{vars}, \{cond} → \{ro} == tlsf_ensure_saved(\{args},before)",
    seq([
      gen,
      strip,
      rw([@class.fun_eq_thm()]),
      gen,
      rw(
        [
          thm("tlsf_ensure_saved"),
          thm("tlsf_ensure_ro"),
          thm("tlsf_ensure_frame"),
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("tlsf_regions_append"),
          thm("tlsf_regions"),
          thm("tlsf_top_cell"),
          thm("tlsf_base"),
        ] +
        lift_rws(),
      ),
      arw(lift_rws() + ac),
    ]),
  )
  ignore(eq)
  let _ = lemma(
    "tlsf_star_forget_heap_eq",
    "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ before : \{heap}, ∀ h : \{heap}, star((h0 : \{heap}) => h0 == before && p(h0),q,h) → star(p,q,h)",
    seq([rw([thm("star")]), @meson.meson_tac(ths([]))]),
  )
}
