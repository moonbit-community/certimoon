///|
fn prove_tlsf_split_close() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let cell = (a : String, v : String) => "pts(\{a}, serialise_i32((\{v} : \{w})))"
  let topcell = cell("val(word_add(tlsf_base((d : " + w + ")), word(1908)))", "top")
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let nh = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let mh = "word_or(word_and((hd : \{ht})((m : \{w})), word(4294967294)), word(1))"
  let bins = "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let payload = "tlsf_bytes(val((m : \{w})) + 8, val(tlsf_size((hd : \{ht})(m))))"
  let oldparts = [topcell, "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))", cell("val((m : " + w + "))", mh), cell("val(word_add((m : " + w + "), word(4)))", "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))"), payload, "tlsf_regions((m : \{w}), (zs : \{lw}), (hd : \{ht}))", bins]
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{hprop})"
    for k = ps.length()-1; k>=0; k=k-1 { s = "star(\{ps[k]}, \{s})" }
    s
  }
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, \{nh}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{hprop}"
  let _ = lemma("tlsf_mark_close", "\{vars}, tlsf_physical_ok(d, lim, top, \{oldxs}, hd) && tlsf_bins_match(\{oldxs}, \{nh}, bl) → \{star(oldparts)} == star(\{large}, star(\{payload}, fp))", seq([
    gen, strip,
    @tactics.mp_tac(inst(thm("tlsf_mark_focus"), ["(ys : \{lw})", "(zs : \{lw})", "(m : \{w})", "(d : \{w})", "(lim : Num)", "(top : \{w})", "(hd : \{ht})"])), arw([]), strip,
    rw([@class.fun_eq_thm()]), gen,
    rw([thm("tlsf_large"), thm("tlsf_chain"), thm("tlsf_regions_append"), thm("tlsf_regions")] + lift_rws()),
    arw([thm("tlsf_spare"), thm("tlsf_used_store_fields")] + lift_rws() + ac),
  ]))
}
