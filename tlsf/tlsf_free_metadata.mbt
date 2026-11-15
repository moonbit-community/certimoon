///|
fn prove_tlsf_free_metadata() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_free_release_live",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_free_live(xs,hd,m,xs,tlsf_release(hd,m))",
    seq([
      gen,
      rw([thm("tlsf_free_live")]),
      gen,
      strip,
      arw([thm("tlsf_release"), thm("tlsf_put")]),
    ]),
  )
  let _ = lemma(
    "tlsf_free_release_covers",
    "∀ hd : \{ht}, ∀ m : \{w}, tlsf_free_covers(m,hd,m,tlsf_release(hd,m))",
    seq([
      gen,
      rw([thm("tlsf_free_covers"), thm("tlsf_free_release_fields")]),
      @int.arith_tac,
    ]),
  )
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS((r : \{w}),(zs : \{lw}))))"
  let nx = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let nh = "tlsf_merge_headers((hd : \{ht}),(m : \{w}),(r : \{w}))"
  let oldbody = "∀ x : \{w}, MEM(x,(xs0 : \{lw})) && !(x == (m0 : \{w})) && tlsf_used((hd0 : \{ht})(x)) → MEM(x,\{xs}) && (hd : \{ht})(x) == hd0(x)"
  let vars = "∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ m0 : \{w}, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}"
  let _ = lemma(
    "tlsf_free_merge_live",
    "\{vars}, tlsf_free_live(xs0,hd0,m0,\{xs},hd) && !tlsf_used(hd(m)) && !tlsf_used(hd(r)) → tlsf_free_live(xs0,hd0,m0,\{nx},\{nh})",
    seq([
      gen,
      rw([thm("tlsf_free_live")]),
      strip,
      @tactics.x_gen_tac(tm("(x : \{w})")),
      strip,
      @tactics.assume_tac(
        inst(@kernel.assume_rule(tm(oldbody)), ["(x : \{w})"]),
      ),
      @tactics.pop_assum_list(all => {
        seq(
          all
          .to_array()
          .filter(th => !@basics.is_forall(@kernel.concl(th)))
          .map(@tactics.assume_tac),
        )
      }),
      free_have(
        "MEM((x : \{w}),\{xs}) && (hd : \{ht})(x) == (hd0 : \{ht})(x)",
        @meson.asm_meson_tac(ths([])),
      ),
      split_conjs(),
      free_have(
        "!((x : \{w}) == (m : \{w})) && !(x == (r : \{w}))",
        @meson.asm_meson_tac(ths([])),
      ),
      split_conjs(),
      arw([
        thm("tlsf_merge_headers"),
        thm("tlsf_put"),
        @lists.mem_append(),
        @lists.mem(),
      ]),
      @meson.asm_meson_tac(ths([@lists.mem_append(), @lists.mem()])),
    ]),
  )
  let _ = lemma(
    "tlsf_free_merge_covers",
    "∀ m0 : \{w}, ∀ hd0 : \{ht}, ∀ active : \{w}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_free_covers(m0,hd0,active,hd) && (active == m || active == r) && val(r) == val(m)+8+val(tlsf_size(hd(m))) && val(tlsf_size(nh(m))) == val(tlsf_size(hd(m)))+8+val(tlsf_size(hd(r))) → tlsf_free_covers(m0,hd0,m,nh)",
    seq([
      gen,
      rw([thm("tlsf_free_covers")]),
      strip,
      subst_vars(),
      @int.asm_arith_tac,
    ]),
  )
}
