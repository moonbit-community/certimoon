// Expose just the two adjacency conditions at the active block.

///|
fn prove_tlsf_free_coalesced() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let _ = lemma(
    "tlsf_coalesced_focus",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ hd : \{ht}, tlsf_coalesced(APPEND(ys,CONS(m,zs)),hd) == (tlsf_coalesced(ys,hd) && tlsf_coalesced(zs,hd) && (ys == NIL || tlsf_used(hd(tlsf_end(word(0),ys))) || tlsf_used(hd(m))) && (zs == NIL || tlsf_used(hd(m)) || tlsf_used(hd(HD(zs)))))",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          @lists.append(),
          thm("tlsf_coalesced"),
          thm("tlsf_end"),
          @lists.not_cons_nil(),
        ]),
        gen,
        @tactics.first(
          @list.List([
            solve(@meson.meson_tac(ths([]))),
            solve(
              seq([
                @tactics.strip_assume_tac(
                  inst(@lists.list_cases(), ["(t : \{lw})"]),
                ),
                subst_vars(),
                arw([
                  @lists.append(),
                  thm("tlsf_coalesced"),
                  thm("tlsf_end"),
                  @lists.hd(),
                  @lists.not_cons_nil(),
                ]),
                @meson.meson_tac(ths([])),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let agree = "∀ x : \{w}, MEM(x,APPEND((ys : \{lw}),(zs : \{lw}))) → (tlsf_used((hd : \{ht})(x)) == tlsf_used((nh : \{ht})(x)))"
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let mono = (xs : String) => {
    seq([
      @tactics.match_mp_tac(
        inst(thm("tlsf_coalesced_mono"), [xs, "(hd : \{ht})", "(nh : \{ht})"]),
      ),
      arw([]),
      @tactics.x_gen_tac(tm("(x : \{w})")),
      strip,
      @tactics.assume_tac(inst(@kernel.assume_rule(tm(agree)), ["(x : \{w})"])),
      @tactics.pop_assum_list(all => {
        seq(
          all
          .to_array()
          .filter(th => !@basics.is_forall(@kernel.concl(th)))
          .map(@tactics.assume_tac),
        )
      }),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.mem_append()]))),
      @meson.asm_meson_tac(ths([])),
    ])
  }
  let _ = lemma(
    "tlsf_coalesced_contract",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_coalesced(APPEND(ys,CONS(m,CONS(r,zs))),hd) && tlsf_used(nh(m)) && (\{agree}) → tlsf_coalesced(APPEND(ys,CONS(m,zs)),nh)",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "tlsf_coalesced((ys : \{lw}),(hd : \{ht})) && tlsf_coalesced((zs : \{lw}),hd)",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_coalesced(APPEND((ys : \{lw}),CONS((m : \{w}),CONS((r : \{w}),(zs : \{lw})))),(hd : \{ht}))",
              ),
            ),
            rw([
              thm("tlsf_coalesced_focus"),
              thm("tlsf_coalesced"),
              @lists.not_cons_nil(),
            ]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        split_conjs(),
        rw([thm("tlsf_coalesced_focus")]),
        arw([]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([mono("(ys : \{lw})"), mono("(zs : \{lw})")]),
        ),
      ])
    },
  )
}
