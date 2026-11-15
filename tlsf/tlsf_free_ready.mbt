///|
fn prove_tlsf_free_ready() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_free_end_member",
    "∀ xs : \{lw}, ∀ p : \{w}, !(xs == NIL) → MEM(tlsf_end(p,xs),xs)",
    seq([
      gen,
      @tactics.strip_assume_tac(inst(thm("snoc_cases"), ["(xs : \{lw})"])),
      subst_vars(),
      rw([
        @lists.mem_append(),
        thm("tlsf_free_end_append"),
        thm("tlsf_end"),
        @lists.mem(),
      ]),
    ]),
  )
  let _ = lemma(
    "tlsf_free_ready_cong",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, (∀ x : \{w}, MEM(x,xs) → (tlsf_used(hd(x)) == tlsf_used(nh(x)))) → ((tlsf_free_left(xs,hd) == tlsf_free_left(xs,nh)) && (tlsf_free_right(xs,hd) == tlsf_free_right(xs,nh)))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.thenl(
        @class.asm_cases_tac(tm("(xs : \{lw}) == NIL")),
        @list.List([
          arw([thm("tlsf_free_left"), thm("tlsf_free_right")]),
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_free_end_member"), [
                "(xs : \{lw})",
                "(word(0) : \{w})",
              ]),
            ),
            arw([]),
            @tactics.disch_tac,
            @tactics.mp_tac(inst(thm("tlsf_mem_hd"), ["(xs : \{lw})"])),
            arw([]),
            @tactics.disch_tac,
            free_have(
              "(tlsf_used((hd : \{ht})(tlsf_end((word(0) : \{w}),(xs : \{lw})))) == tlsf_used((nh : \{ht})(tlsf_end(word(0),xs)))) && (tlsf_used(hd(HD(xs))) == tlsf_used(nh(HD(xs))))",
              @meson.asm_meson_tac(ths([])),
            ),
            split_conjs(),
            arw([thm("tlsf_free_left"), thm("tlsf_free_right")]),
          ]),
        ]),
      ),
    ]),
  )
  for
    (name, pred) in [
      ("tlsf_free_left_transfer", "tlsf_free_left"),
      ("tlsf_free_right_transfer", "tlsf_free_right"),
    ] {
    let _ = lemma(
      name,
      "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ nh : \{ht}, \{pred}(xs,hd) && (∀ x : \{w}, MEM(x,xs) → (tlsf_used(hd(x)) == tlsf_used(nh(x)))) → \{pred}(xs,nh)",
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_ready_cong"), [
            "(xs : \{lw})",
            "(hd : \{ht})",
            "(nh : \{ht})",
          ]),
        ),
        arw([]),
        @tactics.pop_assum_list(all => {
          seq(
            all
            .to_array()
            .filter(th => !@basics.is_forall(@kernel.concl(th)))
            .map(@tactics.assume_tac),
          )
        }),
        @meson.asm_meson_tac(ths([])),
      ]),
    )
  }
  let _ = lemma(
    "tlsf_free_coalesced_neighbours",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ hd : \{ht}, tlsf_coalesced(APPEND(ys,CONS(m,zs)),hd) && !tlsf_used(hd(m)) → tlsf_free_left(ys,hd) && tlsf_free_right(zs,hd)",
    seq([
      gen,
      rw([
        thm("tlsf_coalesced_focus"),
        thm("tlsf_free_left"),
        thm("tlsf_free_right"),
      ]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let marked = "tlsf_mark((hd : \{ht}),(m : \{w}))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  let pre = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht}),(m : \{w})) && tlsf_free_left((ys : \{lw}),hd) && tlsf_free_right((zs : \{lw}),hd)"
  let _ = lemma(
    "tlsf_free_ready_physical",
    "\{vars}, \{pre} → tlsf_physical_ok(d,lim,top,\{xs},hd)",
    seq([
      gen,
      rw([thm("tlsf_free_geom_facts")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_distinct"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          "(m : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      free_have(
        "tlsf_coalesced((ys : \{lw}),\{marked}) && tlsf_coalesced((zs : \{lw}),\{marked})",
        seq([
          @tactics.undisch_tac(tm("tlsf_coalesced(\{xs},\{marked})")),
          rw([thm("tlsf_coalesced_focus")]),
          @meson.meson_tac(ths([])),
        ]),
      ),
      split_conjs(),
      seq(
        ["(ys : \{lw})", "(zs : \{lw})"].map(ls => {
          free_have(
            "tlsf_coalesced(\{ls},(hd : \{ht}))",
            seq([
              @tactics.match_mp_tac(
                inst(thm("tlsf_coalesced_mono"), [ls, marked, "(hd : \{ht})"]),
              ),
              arw([]),
              @tactics.x_gen_tac(tm("(x : \{w})")),
              strip,
              free_have(
                "!((x : \{w}) == (m : \{w}))",
                @meson.asm_meson_tac(ths([])),
              ),
              @tactics.first_x_assum(th => {
                if head_name(@kernel.concl(th)) == "tlsf_used" {
                  @tactics.mp_tac(th)
                } else {
                  @tactics.no_tac
                }
              }),
              arw([thm("tlsf_free_mark_fields")]),
            ]),
          )
        }),
      ),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([thm("tlsf_free_left"), thm("tlsf_free_right")])),
      ),
      arw([
        thm("tlsf_physical_ok"),
        thm("tlsf_coalesced_focus"),
        thm("tlsf_free_left"),
        thm("tlsf_free_right"),
      ]),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}
