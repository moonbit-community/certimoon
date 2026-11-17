///|
fn prove_tlsf_split_coalesced() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_coalesced_mono",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, tlsf_coalesced(xs, hd) && (∀ m : \{w}, MEM(m, xs) && tlsf_used(hd(m)) → tlsf_used(nh(m))) → tlsf_coalesced(xs, nh)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([thm("tlsf_coalesced"), @lists.mem()]),
        gen,
        strip,
        have(
          "tlsf_coalesced((t : \{lw}), (nh : \{ht}))",
          seq([
            @tactics.first_x_assum(th => {
              @tactics.match_mp_tac(inst(th, ["(hd : \{ht})", "(nh : \{ht})"]))
            }),
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(@tactics.first_assum(th => @tactics.accept_tac(th))),
                solve(
                  seq([
                    gen,
                    strip,
                    @tactics.first_x_assum(th => {
                      @tactics.match_mp_tac(@bool.spec(tm("(m : \{w})"), th))
                    }),
                    arw([]),
                  ]),
                ),
              ]),
            ),
          ]),
        ),
        @tactics.first_x_assum(th => {
          let (vs, _) = @basics.strip_forall(@kernel.concl(th))
          if vs.length() == 1 {
            seq([
              @tactics.assume_tac(@bool.spec(tm("(h : \{w})"), th)),
              @tactics.assume_tac(@bool.spec(tm("HD((t : \{lw}))"), th)),
            ])
          } else {
            @tactics.no_tac
          }
        }),
        @tactics.strip_assume_tac(
          @bool.ispec(tm("(t : \{lw})"), @lists.list_cases()),
        ),
        subst_vars(),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(
            ths([@lists.hd(), @lists.mem(), @lists.not_cons_nil()]),
          ),
        ),
        arw([@lists.hd(), @lists.mem(), @lists.not_cons_nil()]),
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
    },
  )
  let _ = lemma(
    "tlsf_hd_splice",
    "∀ ys : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ zs : \{lw}, HD(APPEND(ys, CONS(m, CONS(r, zs)))) == HD(APPEND(ys, CONS(m, zs)))",
    () => seq([@lists.list_induct_tac, rw([@lists.append(), @lists.hd()])]),
  )
  let _ = lemma(
    "tlsf_coalesced_splice",
    "∀ ys : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ zs : \{lw}, ∀ hd : \{ht}, tlsf_coalesced(APPEND(ys, CONS(m, zs)), hd) && tlsf_used(hd(m)) && (zs == NIL || tlsf_used(hd(HD(zs)))) → tlsf_coalesced(APPEND(ys, CONS(m, CONS(r, zs))), hd)",
    () => {
      seq([
        @lists.list_induct_tac,
        rw([
          @lists.append(),
          thm("tlsf_coalesced"),
          @lists.append_eq_nil(),
          @lists.not_cons_nil(),
        ]),
        gen,
        strip,
        arw([]),
        have(
          "tlsf_coalesced(APPEND((t : \{lw}), CONS((m : \{w}), CONS((r : \{w}), (zs : \{lw})))), (hd : \{ht}))",
          seq([
            @tactics.first_x_assum(th => {
              @tactics.match_mp_tac(
                inst(th, [
                  "(m : \{w})",
                  "(r : \{w})",
                  "(zs : \{lw})",
                  "(hd : \{ht})",
                ]),
              )
            }),
            arw([]),
          ]),
        ),
        subst_vars(),
        arw([
          thm("tlsf_hd_splice"),
          @lists.append_eq_nil(),
          @lists.not_cons_nil(),
        ]),
      ])
    },
  )
}
