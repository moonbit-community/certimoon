///|
fn define_tlsf_free_pair() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let ps = [
    cell("tlsf_top_cell((d : " + w + "))", "top"),
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),(hd : \{ht}))",
    cell("m", "(hd : " + ht + ")((m : " + w + "))"),
    cell(
      "word_add((m : " + w + "),word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd : \{ht})(m))))",
    cell("r", "(hd : " + ht + ")((r : " + w + "))"),
    cell("word_add((r : " + w + "),word(4))", "m"),
    "tlsf_bytes(val((r : \{w}))+8,val(tlsf_size((hd : \{ht})(r))))",
    "tlsf_regions((r : \{w}),(zs : \{lw}),(hd : \{ht}))",
    "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
  ]
  let mut out = ps[ps.length() - 1]
  for k = ps.length() - 2; k >= 0; k = k - 1 {
    out = "star(\{ps[k]},\{out})"
  }
  def(
    "tlsf_free_pair",
    "tlsf_free_pair((d : \{w}),(top : \{w}),(ys : \{lw}),(m : \{w}),(r : \{w}),(zs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt})) == \{out}",
  )
  let _ = lemma(
    "tlsf_free_end_append",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ p : \{w}, tlsf_end(p,APPEND(ys,zs)) == tlsf_end(tlsf_end(p,ys),zs)",
    () => {
      seq([
        @lists.list_induct_tac,
        @simp.rewrite_tac(ths([@lists.append(), thm("tlsf_end")])),
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.asm_rewrite_tac(ths([])),
      ])
    },
  )
}
