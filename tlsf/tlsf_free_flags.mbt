///|
fn prove_tlsf_free_flags() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let mark = "tlsf_mark((hd : \{ht}),(m : \{w}))"
  let rel = "tlsf_release((hd : \{ht}),(m : \{w}))"
  for
    (name, nh, used, defs) in [
      (
        "tlsf_free_mark_fields",
        mark,
        "((x : \{w}) == (m : \{w}) || tlsf_used((hd : \{ht})(x)))",
        [thm("tlsf_mark"), thm("tlsf_used_store_fields")],
      ),
      (
        "tlsf_free_release_fields",
        rel,
        "(!((x : \{w}) == (m : \{w})) && tlsf_used((hd : \{ht})(x)))",
        [thm("tlsf_release"), thm("tlsf_release_fields")],
      ),
    ] {
    let _ = lemma(
      name,
      "∀ hd : \{ht}, ∀ m : \{w}, ∀ x : \{w}, tlsf_size((\{nh})(x)) == tlsf_size(hd(x)) && (tlsf_last((\{nh})(x)) == tlsf_last(hd(x))) && (tlsf_used((\{nh})(x)) == \{used})",
      () => {
        seq([
          gen,
          @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")),
          subst_vars(),
          arw(defs + [thm("tlsf_put")]),
        ])
      },
    )
  }
  let eq = lemma(
    "tlsf_free_layout_mark",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_layout(p,a,lim,top,xs,\{mark}) == tlsf_layout(p,a,lim,top,xs,hd)",
    () => {
      seq([
        gen,
        @tactics.match_mp_tac(thm("tlsf_layout_fields")),
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_free_mark_fields")]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_geom_facts",
    "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_free_geom(d,lim,top,xs,hd,m) == (val(d) <= 4294965088 && lim <= 4294967296 && MOD(lim,65536) == 0 && !(xs == NIL) && tlsf_layout(word(0),tlsf_origin(d),lim,top,xs,hd) && tlsf_coalesced(xs,\{mark}))",
    () => rw([thm("tlsf_free_geom"), thm("tlsf_physical_ok"), eq]),
  )
}
