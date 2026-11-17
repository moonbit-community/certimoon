///|
fn prove_tlsf_free_merge_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let hd = "(hd : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let a = "(active : \{w})"
  let old = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},(zs : \{lw}))))"
  let nx = "APPEND((ys : \{lw}),CONS(\{m},(zs : \{lw})))"
  let nt = "(if (zs : \{lw}) == NIL { \{m} } else { (top : \{w}) })"
  let nh = "tlsf_merge_headers(\{hd},\{m},\{r})"
  let marked = "tlsf_mark(\{nh},\{m})"
  let sm = "val(tlsf_size(\{hd}(\{m})))"
  let sr = "val(tlsf_size(\{hd}(\{r})))"
  let snew = "val(tlsf_size((\{nh})(\{m})))"
  let agree = "∀ x : \{w}, MEM(x,APPEND((ys : \{lw}),(zs : \{lw}))) → \{hd}(x) == (\{nh})(x)"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ active : \{w}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  let pre = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{old},\{hd},\{a}) && (active == m || active == r) && !tlsf_used(hd(m)) && !tlsf_used(hd(r))"
  let out = "tlsf_free_geom((d : \{w}),(lim : Num),\{nt},\{nx},\{nh},\{m}) && !tlsf_used((\{nh})(m)) && \{snew} == \{sm}+8+\{sr} && (tlsf_last((\{nh})(m)) == tlsf_last(hd(r))) && (\{agree}) && !(m == r) && !MEM(m,ys) && !MEM(m,zs) && !MEM(r,ys) && !MEM(r,zs)"
  let _ = lemma("tlsf_free_merge_model", "\{vars}, \{pre} → \{out}", () => {
    seq([
      gen,
      rw([thm("tlsf_free_geom_facts")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_free_pair_facts"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          m,
          r,
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([]),
      strip,
      free_have(
        "MOD(\{sm},8) == 0 && MOD(\{sr},8) == 0 && 16 <= \{sm} && 16 <= \{sr}",
        seq([
          @tactics.undisch_tac(
            tm("tlsf_block_ok(val(\{m}),(lim : Num),\{m},\{hd})"),
          ),
          @tactics.undisch_tac(
            tm("tlsf_block_ok(val(\{r}),(lim : Num),\{r},\{hd})"),
          ),
          rw([thm("tlsf_block_ok")]),
          strip,
          strip,
          arw([]),
        ]),
      ),
      split_conjs(),
      @tactics.mp_tac(
        inst(thm("tlsf_merge_header_fields"), ["\{hd}(\{m})", "\{hd}(\{r})"]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_merge_size_fields"), ["\{hd}(\{m})", "\{hd}(\{r})"]),
      ),
      arw([]),
      strip,
      free_have(
        agree,
        seq([
          @tactics.x_gen_tac(tm("(x : \{w})")),
          @tactics.disch_tac,
          free_have(
            "!((x : \{w}) == \{m}) && !(x == \{r})",
            @meson.asm_meson_tac(ths([@lists.mem_append()])),
          ),
          split_conjs(),
          arw([thm("tlsf_merge_headers"), thm("tlsf_put")]),
        ]),
      ),
      free_have(
        "tlsf_layout((word(0) : \{w}),tlsf_origin((d : \{w})),(lim : Num),\{nt},\{nx},\{nh})",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_contract"), [
              "(ys : \{lw})",
              "(zs : \{lw})",
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(lim : Num)",
              "(top : \{w})",
              m,
              r,
              hd,
              nh,
            ]),
          ),
          arw([thm("tlsf_merge_headers"), thm("tlsf_put")]),
          @tactics.repeat_tac(@tactics.conj_tac),
          @tactics.first(
            @list.List([
              solve(@int.asm_arith_tac),
              solve(
                seq([@tactics.match_mp_tac(thm("tlsf_merge_aligned")), arw([])]),
              ),
            ]),
          ),
        ]),
      ),
      free_have(
        "tlsf_coalesced(\{nx},\{marked})",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_coalesced_contract"), [
              "(ys : \{lw})",
              "(zs : \{lw})",
              m,
              r,
              "tlsf_mark(\{hd},\{a})",
              marked,
            ]),
          ),
          arw([thm("tlsf_free_mark_fields")]),
          @tactics.x_gen_tac(tm("(x : \{w})")),
          @tactics.disch_tac,
          free_have(
            "!((x : \{w}) == \{m}) && !(x == \{r}) && !(x == \{a})",
            @meson.asm_meson_tac(ths([@lists.mem_append()])),
          ),
          split_conjs(),
          free_have(
            "\{hd}((x : \{w})) == (\{nh})(x)",
            @meson.asm_meson_tac(ths([])),
          ),
          arw([thm("tlsf_free_mark_fields")]),
        ]),
      ),
      arw([
        thm("tlsf_merge_headers"),
        thm("tlsf_put"),
        @lists.append_eq_nil(),
        @lists.not_cons_nil(),
      ]),
      @int.asm_arith_tac,
    ])
  })
}
