///|
fn prove_tlsf_free_pair_geometry() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let packet = inst(thm("tlsf_free_pair_facts"), [
    "(ys : \{lw})",
    "(zs : \{lw})",
    "(m : \{w})",
    "(r : \{w})",
    "(word(0) : \{w})",
    "tlsf_origin((d : \{w}))",
    "(lim : Num)",
    "(top : \{w})",
    "(hd : \{ht})",
  ])
  let out = @basics.dest_imp(@kernel.concl(packet)).1
  let _ = lemma(
    "tlsf_free_pair_geometry",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ active : \{w}, tlsf_free_geom(d,lim,top,APPEND(ys,CONS(m,CONS(r,zs))),hd,active) → \{show(out)}",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(packet),
      @tactics.first_x_assum(th => {
        @tactics.mp_tac(
          @simp.rewrite_rule(ths([thm("tlsf_free_geom_facts")]))(th),
        )
      }),
      @meson.meson_tac(ths([])),
    ]),
  )
}
