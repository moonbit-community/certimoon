///|
fn prove_tlsf_free_structure() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_release_fields",
    "∀ h : \{w}, tlsf_size(word_and(h,word(4294967294))) == tlsf_size(h) && (tlsf_last(word_and(h,word(4294967294))) == tlsf_last(h)) && !tlsf_used(word_and(h,word(4294967294)))",
    seq([
      gen,
      rw([
        thm("tlsf_size"),
        thm("tlsf_last"),
        thm("tlsf_used"),
        thm("tlsf_and_assoc"),
      ]),
      @tactics.conv_tac(@words.word_reduce_conv),
      rw([@words.word_and_0()]),
    ]),
  )
  let _ = lemma(
    "tlsf_layout_fields",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, (∀ x : \{w}, MEM(x,xs) → tlsf_size(hd(x)) == tlsf_size(nh(x)) && (tlsf_last(hd(x)) == tlsf_last(nh(x)))) → (tlsf_layout(p,a,lim,top,xs,hd) == tlsf_layout(p,a,lim,top,xs,nh))",
    seq([
      @lists.list_induct_tac,
      rw([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.mem()]),
      gen,
      @tactics.disch_tac,
      free_have(
        "tlsf_size((hd : \{ht})((h : \{w}))) == tlsf_size((nh : \{ht})(h)) && (tlsf_last(hd(h)) == tlsf_last(nh(h)))",
        @meson.asm_meson_tac(ths([])),
      ),
      free_have(
        "∀ x : \{w}, MEM(x,(t : \{lw})) → tlsf_size((hd : \{ht})(x)) == tlsf_size((nh : \{ht})(x)) && (tlsf_last(hd(x)) == tlsf_last(nh(x)))",
        @meson.asm_meson_tac(ths([])),
      ),
      free_have(
        "tlsf_layout((h : \{w}),(a : Num)+8+val(tlsf_size((nh : \{ht})(h))),(lim : Num),(top : \{w}),(t : \{lw}),(hd : \{ht})) == tlsf_layout(h,a+8+val(tlsf_size(nh(h))),lim,top,t,nh)",
        seq([
          @tactics.first_x_assum(th => {
            @tactics.match_mp_tac(
              inst(th, [
                "(h : \{w})",
                "(a : Num)+8+val(tlsf_size((nh : \{ht})((h : \{w}))))",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(nh : \{ht})",
              ]),
            )
          }),
          arw([]),
        ]),
      ),
      arw([]),
    ]),
  )
  let bm = "tlsf_bins_match((xs : \{lw}),(hd : \{ht}),(bl : \{bt}))"
  let rel = "∀ x : \{w}, (MEM(x,(xs : \{lw})) && !tlsf_used((hd : \{ht})(x))) == (MEM(x,(ys : \{lw})) && !tlsf_used((nh : \{ht})(x)))"
  let agree = "∀ x : \{w}, MEM(x,(xs : \{lw})) && !tlsf_used((hd : \{ht})(x)) → hd(x) == (nh : \{ht})(x)"
  let cov = @bool.conjunct1(
    @simp.rewrite_rule(ths([thm("tlsf_bins_match")]))(
      @kernel.assume_rule(tm(bm)),
    ),
  )
  let snd = @bool.conjunct2(
    @simp.rewrite_rule(ths([thm("tlsf_bins_match")]))(
      @kernel.assume_rule(tm(bm)),
    ),
  )
  let ground = seq([
    @tactics.pop_assum_list(all => {
      seq(
        all
        .to_array()
        .filter(th => !@basics.is_forall(@kernel.concl(th)))
        .map(@tactics.assume_tac),
      )
    }),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "tlsf_free_bins_transport",
    "∀ xs : \{lw}, ∀ ys : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, ∀ bl : \{bt}, \{bm} && (\{rel}) && (\{agree}) → tlsf_bins_match(ys,nh,bl)",
    seq([
      gen,
      strip,
      rw([thm("tlsf_bins_match")]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.x_gen_tac(tm("(x : \{w})")),
            strip,
            @tactics.assume_tac(inst(cov, ["(x : \{w})"])),
            @tactics.assume_tac(
              inst(@kernel.assume_rule(tm(rel)), ["(x : \{w})"]),
            ),
            @tactics.assume_tac(
              inst(@kernel.assume_rule(tm(agree)), ["(x : \{w})"]),
            ),
            ground,
          ]),
          seq([
            @tactics.x_gen_tac(tm("(f : Num)")),
            @tactics.x_gen_tac(tm("(j : Num)")),
            @tactics.x_gen_tac(tm("(x : \{w})")),
            strip,
            @tactics.assume_tac(
              inst(snd, ["(f : Num)", "(j : Num)", "(x : \{w})"]),
            ),
            @tactics.assume_tac(
              inst(@kernel.assume_rule(tm(rel)), ["(x : \{w})"]),
            ),
            @tactics.assume_tac(
              inst(@kernel.assume_rule(tm(agree)), ["(x : \{w})"]),
            ),
            ground,
          ]),
        ]),
      ),
    ]),
  )
}
