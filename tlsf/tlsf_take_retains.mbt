// Retain old used memories explicitly, so higher-level page invariants can
// be transported through take, including a split before an existing page.

///|
fn define_tlsf_take_retains() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  def(
    "tlsf_retains",
    "tlsf_retains((xs : \{lw}),(hd : \{ht}),(xs2 : \{lw}),(hd2 : \{ht})) == (∀ x : \{w}, MEM(x,xs) && tlsf_used(hd(x)) → MEM(x,xs2) && hd2(x) == hd(x))",
  )
}

///|
fn prove_tlsf_take_retains() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))

  let _ = lemma(
    "tlsf_retains_mark",
    "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ m : \{w}, !tlsf_used(hd(m)) → tlsf_retains(xs,hd,xs,tlsf_mark(hd,m))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_retains")]),
        strip,
        gen,
        strip,
        free_have("!((x : \{w}) == (m : \{w}))", @meson.asm_meson_tac(ths([]))),
        arw([thm("tlsf_mark"), thm("tlsf_put")]),
      ])
    },
  )
  let oldxs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let r = "tlsf_remainder((m : \{w}),(n : \{w}))"
  let newxs = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS(\{r},(zs : \{lw}))))"
  let _ = lemma(
    "tlsf_retains_split",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ hd : \{ht}, ∀ m : \{w}, ∀ n : \{w}, !tlsf_used(hd(m)) && !MEM(\{r},\{oldxs}) → tlsf_retains(\{oldxs},hd,\{newxs},tlsf_split_headers(hd,m,n))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_retains")]),
        strip,
        gen,
        strip,
        free_have(
          "!((x : \{w}) == (m : \{w})) && !(x == \{r})",
          @meson.asm_meson_tac(ths([])),
        ),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(ths([@lists.mem_append(), @lists.mem()])),
        ),
        arw([
          thm("tlsf_split_headers"),
          thm("tlsf_put"),
          @lists.mem_append(),
          @lists.mem(),
        ]),
        @meson.asm_meson_tac(ths([])),
      ])
    },
  )
}
