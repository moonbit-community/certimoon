///|
fn define_tlsf_initialize_growth_state() -> Unit raise {
  let args = "(d : \{w32}),(lim : Num),(before : \{heap}),(fp : \{rty})"
  def(
    "tlsf_initialize_saved",
    "tlsf_initialize_saved(\{args}) == ((gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && h == before && star(tlsf_initialize_zero(d,lim),fp(gs,lim),h))",
  )
  def(
    "tlsf_initialize_fresh",
    "tlsf_initialize_fresh((d : \{w32}),(lim : Num),(fp : \{rty})) == ((gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == tlsf_initialize_limit(d,lim) && star(tlsf_initialize_zero(d,ms),fp(gs,lim),h))",
  )
}

///|
fn prove_tlsf_initialize_grown_zero() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let base = "val(tlsf_base(\{d}))"
  let rep = (n : String) => "REPLICATE(\{n},(word(0) : Word[8]))"
  let _ = lemma(
    "tlsf_initialize_zero_join",
    "∀ d : \{w}, ∀ lim : Num, ∀ k : Num, \{base} <= lim → star(tlsf_initialize_zero(d,lim),pts(lim,\{rep("k")})) == tlsf_initialize_zero(d,lim+k)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have("\{base}+(\{lim}-\{base}) == \{lim}", @int.asm_arith_tac),
        free_have(
          "(\{lim}-\{base})+(k : Num) == lim+k-\{base}",
          @int.asm_arith_tac,
        ),
        @tactics.mp_tac(
          inst(thm("pts_split"), [
            base,
            rep("(lim : Num)-" + base),
            rep("(k : Num)"),
          ]),
        ),
        rw([
          @equal.gsym(thm("tlsf_replicate_add")),
          @lists.length_replicate(),
          thm("tlsf_initialize_zero"),
        ]),
        arw([]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let saved = "tlsf_initialize_saved(\{d},\{lim},(before : \{heap}),(fp : \{rty}))((gs : List[Value]),\{lim})"
  let client = "(fp : \{rty})((gs : List[Value]),\{lim})"
  let grow = "pts(\{lim},\{rep("(k : Num)")})"
  let old = "tlsf_initialize_zero(\{d},\{lim})"
  let perm = @logic.prove(
    tm(
      "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ r : \{hprop}, star(star(p,q),r) == star(star(p,r),q)",
    ),
    rw([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
  )
  let _ = lemma(
    "tlsf_initialize_grown_zero_frame",
    "∀ d : \{w}, ∀ lim : Num, ∀ k : Num, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ gs : List[Value], ∀ h : \{heap}, \{base} <= lim && star(\{saved},\{grow},h) → star(tlsf_initialize_zero(d,lim+k),\{client},h)",
    () => {
      seq([
        gen,
        strip,
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(ths([thm("tlsf_initialize_saved")])),
        ),
        free_have(
          "star(star(\{old},\{client}),\{grow},(h : \{heap}))",
          seq([
            @tactics.match_mp_tac(thm("star_mono")),
            @tactics.exists_tac(tm(saved)),
            @tactics.exists_tac(tm(grow)),
            rw([thm("tlsf_initialize_saved")]),
            @meson.asm_meson_tac(ths([])),
          ]),
        ),
        @tactics.undisch_tac(
          tm("star(star(\{old},\{client}),\{grow},(h : \{heap}))"),
        ),
        @tactics.subst1_tac(inst(perm, [old, client, grow])),
        @simp.asm_simp_tac(ths([thm("tlsf_initialize_zero_join")])),
      ])
    },
  )
}
