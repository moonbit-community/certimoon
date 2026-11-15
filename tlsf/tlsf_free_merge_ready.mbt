///|
fn prove_tlsf_free_merge_ready() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let hd = "(hd : \{ht})"
  let nh = "tlsf_merge_headers(\{hd},\{m},\{r})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},(zs : \{lw}))))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let marked = "tlsf_mark(\{hd},\{active})"
    let geom = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active})"
    let cond = "\{geom} && !tlsf_used(\{hd}(\{m})) && !tlsf_used(\{hd}(\{r}))" +
      (if prev {
        ""
      } else {
        " && tlsf_free_left((ys : " + lw + ")," + hd + ")"
      })
    let out = "tlsf_free_left((ys : \{lw}),\{nh})" +
      (if prev {
        ""
      } else {
        " && tlsf_free_right((zs : " + lw + ")," + nh + ")"
      })
    let pfx = if prev { "(ys : \{lw})" } else { "APPEND((ys : \{lw}),[\{m}])" }
    let focus = if prev { m } else { r }
    let suffix = if prev { "CONS(\{r},(zs : \{lw}))" } else { "(zs : \{lw})" }
    let point = (ls : String, src : String) => {
      seq([
        @tactics.x_gen_tac(tm("(x : \{w})")),
        @tactics.disch_tac,
        free_have(
          "!((x : \{w}) == \{m}) && !(x == \{r})",
          @meson.asm_meson_tac(ths([])),
        ),
        split_conjs(),
        arw([
          thm("tlsf_free_mark_fields"),
          thm("tlsf_merge_headers"),
          thm("tlsf_put"),
        ]),
      ])
    }
    let left = seq([
      @tactics.match_mp_tac(
        inst(thm("tlsf_free_left_transfer"), [
          "(ys : \{lw})",
          if prev {
            marked
          } else {
            hd
          },
          nh,
        ]),
      ),
      arw([]),
      point("(ys : \{lw})", if prev { marked } else { hd }),
    ])
    let right = seq([
      @tactics.match_mp_tac(
        inst(thm("tlsf_free_right_transfer"), ["(zs : \{lw})", marked, nh]),
      ),
      arw([]),
      point("(zs : \{lw})", marked),
    ])
    let _ = lemma(
      if prev {
        "tlsf_free_merge_prev_ready"
      } else {
        "tlsf_free_merge_next_ready"
      },
      "\{vars}, \{cond} → \{out}",
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
          @simp.rewrite_rule(ths([thm("tlsf_free_geom_facts")]))(
            @kernel.assume_rule(tm(geom)),
          ),
        ),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_coalesced_neighbours"), [
            pfx, suffix, focus, marked,
          ]),
        ),
        arw([
          @equal.gsym(@lists.append_assoc()),
          @lists.append(),
          thm("tlsf_free_mark_fields"),
        ]),
        strip,
        if prev {
          left
        } else {
          @tactics.thenl(@tactics.conj_tac, @list.List([left, right]))
        },
      ]),
    )
  }
}
