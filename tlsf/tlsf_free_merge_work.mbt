// Pure progress for the two coalescing phases, including the original
// allocation's extent and all other live physical headers.

///|
fn prove_tlsf_free_merge_work() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},(zs : \{lw}))))"
  let nx = "APPEND((ys : \{lw}),CONS(\{m},(zs : \{lw})))"
  let nh = "tlsf_merge_headers(\{hd},\{m},\{r})"
  let nt = "(if (zs : \{lw}) == NIL { \{m} } else { (top : \{w}) })"
  let vars = "∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ m0 : \{w}, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let other = if prev { m } else { r }
    let h = "\{hd}(\{other})"
    let nb = "tlsf_pop_bl(\{h},(bl : \{bt}),APPEND((us : \{lw}),(vs : \{lw})))"
    let pre = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active}) && !tlsf_used(\{hd}(\{m})) && !tlsf_used(\{hd}(\{r})) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{active}),(bl : \{bt})) && tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),\{active},\{hd}) && tlsf_free_live((xs0 : \{lw}),hd0,m0,\{xs},hd) && (bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h})) == APPEND((us : \{lw}),CONS(\{other},(vs : \{lw})))" +
      (if prev { "" } else { " && tlsf_free_left((ys : " + lw + "),hd)" })
    let post = "tlsf_free_geom((d : \{w}),(lim : Num),\{nt},\{nx},\{nh},\{m}) && !tlsf_used((\{nh})(m)) && tlsf_bins_match(\{nx},tlsf_mark(\{nh},\{m}),\{nb}) && tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),\{m},\{nh}) && tlsf_free_live((xs0 : \{lw}),hd0,m0,\{nx},\{nh}) && tlsf_free_left((ys : \{lw}),\{nh})" +
      (if prev {
        ""
      } else {
        " && tlsf_free_right((zs : " + lw + ")," + nh + ")"
      })
    let _ = lemma(
      if prev {
        "tlsf_free_merge_prev_work"
      } else {
        "tlsf_free_merge_next_work"
      },
      "\{vars}, \{pre} → \{post}",
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_merge_model"), [
            "(ys : \{lw})",
            "(zs : \{lw})",
            m,
            r,
            active,
            "(d : \{w})",
            "(lim : Num)",
            "(top : \{w})",
            hd,
          ]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_pop_bins_pair"), [
            xs,
            hd,
            "(bl : \{bt})",
            active,
            other,
            "(us : \{lw})",
            "(vs : \{lw})",
          ]),
        ),
        arw([@lists.mem_append(), @lists.mem()]),
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_free_merge_bins"), [
            "(ys : \{lw})",
            "(zs : \{lw})",
            m,
            r,
            active,
            other,
            hd,
            nb,
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(
            thm(
              if prev {
                "tlsf_free_merge_prev_ready"
              } else {
                "tlsf_free_merge_next_ready"
              },
            ),
            [
              "(ys : \{lw})",
              "(zs : \{lw})",
              m,
              r,
              "(d : \{w})",
              "(lim : Num)",
              "(top : \{w})",
              hd,
            ],
          ),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_merge_live"), [
            "(xs0 : \{lw})",
            "(hd0 : \{ht})",
            "(m0 : \{w})",
            "(ys : \{lw})",
            "(zs : \{lw})",
            m,
            r,
            hd,
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        @tactics.mp_tac(
          inst(thm("tlsf_free_pair_geometry"), [
            "(ys : \{lw})",
            "(zs : \{lw})",
            m,
            r,
            "(d : \{w})",
            "(lim : Num)",
            "(top : \{w})",
            hd,
            active,
          ]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_merge_covers"), [
            "(m0 : \{w})",
            "(hd0 : \{ht})",
            active,
            m,
            r,
            hd,
            nh,
          ]),
        ),
        arw([]),
        @tactics.disch_tac,
        arw([]),
      ]),
    )
  }
}
