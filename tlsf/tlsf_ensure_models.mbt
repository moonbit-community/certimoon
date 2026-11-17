///|
fn prove_tlsf_ensure_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let xs = "APPEND((ys : \{lw}),[(m : \{w})])"
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),(m : \{w}),\{xs},(hd : \{ht}))"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ nextlim : Num, ∀ m : \{w}, ∀ hd : \{ht}"
  let args = [
    "(ys : \{lw})",
    "(d : \{w})",
    "(lim : Num)",
    "(m : \{w})",
    "(hd : \{ht})",
  ]
  let bounds = "(nextlim : Num) <= 4294967296 && MOD(nextlim,65536) == 0"
  let nh = "tlsf_extend_headers((hd : \{ht}),(m : \{w}),(nextlim : Num))"
  let cap = "tlsf_capacity_at((nextlim : Num),(m : \{w}))"
  let agree = "∀ x : \{w}, MEM(x,(ys : \{lw})) → (hd : \{ht})(x) == (\{nh})(x)"
  let pre = "\{old} && !tlsf_used((hd : \{ht})((m : \{w}))) && (lim : Num) <= (nextlim : Num) && \{bounds}"
  let _ = lemma(
    "tlsf_extend_model",
    "\{vars}, \{pre} → tlsf_physical_ok(d,nextlim,m,\{xs},\{nh}) && (\{agree}) && (\{nh})(m) == word_or(\{cap},word_and(hd(m),word(3))) && !tlsf_used((\{nh})(m)) && tlsf_size((\{nh})(m)) == \{cap}",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_ensure_top_facts"), args)),
        arw([]),
        strip,
        have(
          "MOD((nextlim : Num),8) == 0",
          seq([@tactics.match_mp_tac(thm("tlsf_page_aligned8")), arw([])]),
        ),
        have("val((m : \{w}))+24 <= (nextlim : Num)", @int.asm_arith_tac),
        @tactics.mp_tac(
          inst(thm("tlsf_capacity_fields"), ["(nextlim : Num)", "(m : \{w})"]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_resized_fields"), [cap, "(hd : \{ht})((m : \{w}))"]),
        ),
        arw([]),
        strip,
        have(
          agree,
          seq([
            gen,
            @tactics.disch_tac,
            have("!((x : \{w}) == (m : \{w}))", @meson.asm_meson_tac(ths([]))),
            rw([thm("tlsf_extend_headers"), thm("tlsf_put")]),
            arw([]),
          ]),
        ),
        have(
          "(\{nh})((m : \{w})) == word_or(\{cap},word_and((hd : \{ht})(m),word(3)))",
          rw([thm("tlsf_extend_headers"), thm("tlsf_put")]),
        ),
        arw([]),
        @tactics.match_mp_tac(
          inst(thm("tlsf_physical_extend_last"), [
            "(ys : \{lw})",
            "(d : \{w})",
            "(lim : Num)",
            "(nextlim : Num)",
            "(m : \{w})",
            "(hd : \{ht})",
            nh,
          ]),
        ),
        arw([]),
      ])
    },
  )
  let r = "(word((lim : Num)) : \{w})"
  let na = "tlsf_append_headers((hd : \{ht}),(m : \{w}),(lim : Num),(nextlim : Num))"
  let ca = "tlsf_capacity_at((nextlim : Num),\{r})"
  let ag = "∀ x : \{w}, MEM(x,(ys : \{lw})) → (hd : \{ht})(x) == (\{na})(x)"
  let appr = "\{old} && tlsf_used((hd : \{ht})((m : \{w}))) && (lim : Num)+24 <= (nextlim : Num) && \{bounds}"
  let _ = lemma(
    "tlsf_append_model",
    "\{vars}, \{appr} → tlsf_physical_ok(d,nextlim,\{r},APPEND(ys,[m,\{r}]),\{na}) && (\{ag}) && (\{na})(m) == word_and(hd(m),word(4294967293)) && (\{na})(\{r}) == word_or(\{ca},word(2)) && !tlsf_used((\{na})(\{r})) && tlsf_size((\{na})(\{r})) == \{ca} && val(\{r}) == lim && !MEM(\{r},\{xs})",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_ensure_top_facts"), args)),
        arw([]),
        strip,
        have("(lim : Num) < 4294967296", @int.asm_arith_tac),
        have(
          "val(\{r}) == (lim : Num)",
          seq([
            rw([@words.val_word(), @words.dimindex_32()]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            @simp.asm_simp_tac(ths([@arith.mod_lt()])),
          ]),
        ),
        have(
          "!(\{r} == (m : \{w}))",
          seq([rw([@equal.gsym(@words.val_eq())]), arw([]), @int.asm_arith_tac]),
        ),
        have(
          "!MEM(\{r},\{xs})",
          seq([
            @tactics.disch_tac,
            @tactics.mp_tac(inst(thm("tlsf_ensure_old_bound"), args + [r])),
            arw([]),
            @int.arith_tac,
          ]),
        ),
        have(
          "MOD((nextlim : Num),8) == 0 && MOD((lim : Num),8) == 0",
          seq([
            @tactics.conj_tac,
            @tactics.match_mp_tac(thm("tlsf_page_aligned8")),
            arw([]),
          ]),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        have("0 < val(\{r})", seq([arw([]), @int.asm_arith_tac])),
        @tactics.mp_tac(
          inst(thm("tlsf_capacity_fields"), ["(nextlim : Num)", r]),
        ),
        arw([]),
        strip,
        @tactics.mp_tac(inst(thm("tlsf_new_top_fields"), [ca])),
        arw([]),
        strip,
        @tactics.assume_tac(
          inst(thm("tlsf_clear_last_fields"), ["(hd : \{ht})((m : \{w}))"]),
        ),
        have(
          ag,
          seq([
            gen,
            @tactics.disch_tac,
            have(
              "!((x : \{w}) == (m : \{w})) && !(x == \{r})",
              @meson.asm_meson_tac(ths([@lists.mem_append(), @lists.mem()])),
            ),
            rw([thm("tlsf_append_headers"), thm("tlsf_put")]),
            arw([]),
          ]),
        ),
        have(
          "(\{na})((m : \{w})) == word_and((hd : \{ht})(m),word(4294967293)) && (\{na})(\{r}) == word_or(\{ca},word(2))",
          seq([
            rw([thm("tlsf_append_headers"), thm("tlsf_put")]),
            arw([]),
            @meson.asm_meson_tac(ths([])),
          ]),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw([]),
        @tactics.match_mp_tac(
          inst(thm("tlsf_physical_append_last"), [
            "(ys : \{lw})",
            "(d : \{w})",
            "(lim : Num)",
            "(nextlim : Num)",
            "(m : \{w})",
            "(hd : \{ht})",
            na,
            r,
          ]),
        ),
        arw([]),
        @int.asm_arith_tac,
      ])
    },
  )
}
