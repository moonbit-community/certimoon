// Removing either free neighbour leaves both merge inputs absent from
// the bins. Contracting their physical entries changes no remaining free
// address or size class.

///|
fn prove_tlsf_free_merge_bins() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let old = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS((r : \{w}),(zs : \{lw}))))"
  let nx = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let blocked = "tlsf_mark(tlsf_mark((hd : \{ht}),(a : \{w})),(b : \{w}))"
  let nh = "tlsf_merge_headers((hd : \{ht}),(m : \{w}),(r : \{w}))"
  let marked = "tlsf_mark(\{nh},(m : \{w}))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ a : \{w}, ∀ b : \{w}, ∀ hd : \{ht}, ∀ bl : \{bt}"
  let pre = "tlsf_bins_match(\{old},\{blocked},(bl : \{bt})) && (((a : \{w}) == m && (b : \{w}) == r) || (a == r && b == m)) && !(m == r) && !MEM(r,ys) && !MEM(r,zs)"
  let flags = [thm("tlsf_free_mark_fields")]
  let maps = [thm("tlsf_mark"), thm("tlsf_merge_headers"), thm("tlsf_put")]
  let cases = seq([
    @class.asm_cases_tac(tm("(x : \{w}) == (m : \{w})")),
    @class.asm_cases_tac(tm("(x : \{w}) == (r : \{w})")),
    subst_vars(),
  ])
  let _ = lemma(
    "tlsf_free_merge_bins",
    "\{vars}, \{pre} → tlsf_bins_match(\{nx},\{marked},bl)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(
        inst(thm("tlsf_free_bins_transport"), [
          old,
          nx,
          blocked,
          marked,
          "(bl : \{bt})",
        ]),
      ),
      arw([]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.x_gen_tac(tm("(x : \{w})")),
            cases,
            arw(flags + [@lists.mem_append(), @lists.mem()] + maps),
            @meson.asm_meson_tac(ths([])),
          ]),
          seq([
            @tactics.x_gen_tac(tm("(x : \{w})")),
            strip,
            free_have(
              "!((x : \{w}) == (m : \{w})) && !(x == (r : \{w}))",
              seq([
                @tactics.first_x_assum(th => {
                  if head_name(@kernel.concl(th)) == "~" {
                    @tactics.mp_tac(th)
                  } else {
                    @tactics.no_tac
                  }
                }),
                rw(flags),
                @meson.meson_tac(ths([])),
              ]),
            ),
            split_conjs(),
            arw(maps),
          ]),
        ]),
      ),
    ]),
  )
}
