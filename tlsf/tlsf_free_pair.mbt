// Geometry of an adjacent pair, independent of coalescing flags.

///|
fn prove_tlsf_free_pair() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS((r : \{w}),(zs : \{lw}))))"
  let hd = "(hd : \{ht})"
  let sm = "val(tlsf_size(\{hd}((m : \{w}))))"
  let sr = "val(tlsf_size(\{hd}((r : \{w}))))"
  let old = "tlsf_layout((p : \{w}),(a : Num),(lim : Num),(top : \{w}),\{xs},\{hd})"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}"
  let b1 = "tlsf_block_ok(val((m : \{w})),(lim : Num),m,\{hd})"
  let b2 = "tlsf_block_ok(val((r : \{w})),(lim : Num),r,\{hd})"
  let out = "\{b1} && \{b2} && val((r : \{w})) == val((m : \{w}))+8+\{sm} && !tlsf_last(\{hd}(m)) && (tlsf_last(hd(r)) == ((zs : \{lw}) == NIL)) && !MEM(m,ys) && !MEM(m,zs) && !MEM(r,ys) && !MEM(r,zs) && !(m == r) && \{sm}+\{sr}+8 < 4294967296"
  let _ = lemma(
    "tlsf_free_pair_facts",
    "\{vars}, \{old} && lim <= 4294967296 → \{out}",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_distinct"), [
          "(ys : \{lw})",
          "CONS((r : \{w}),(zs : \{lw}))",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([]),
      rw([@lists.mem()]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_distinct"), [
          "APPEND((ys : \{lw}),[(m : \{w})])",
          "(zs : \{lw})",
          "(r : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([
        @equal.gsym(@lists.append_assoc()),
        @lists.append(),
        @lists.mem_append(),
        @lists.mem(),
      ]),
      strip,
      free_have(
        b1,
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_members"), [
              xs,
              "(p : \{w})",
              "(a : Num)",
              "(lim : Num)",
              "(top : \{w})",
              hd,
              "(m : \{w})",
            ]),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
        ]),
      ),
      free_have(
        b2,
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_members"), [
              xs,
              "(p : \{w})",
              "(a : Num)",
              "(lim : Num)",
              "(top : \{w})",
              hd,
              "(r : \{w})",
            ]),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_layout_cut_at"), [
          "(ys : \{lw})",
          "CONS((r : \{w}),(zs : \{lw}))",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "(lim : Num)",
          "(top : \{w})",
          hd,
        ]),
      ),
      arw([]),
      strip,
      @tactics.undisch_tac(
        tm(
          "tlsf_layout(tlsf_end((p : \{w}),(ys : \{lw})),val((m : \{w})),(lim : Num),(top : \{w}),CONS(m,CONS((r : \{w}),(zs : \{lw}))),(hd : \{ht}))",
        ),
      ),
      rw([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]),
      strip,
      arw([]),
      free_have("!(val((m : \{w})) == 0)", arw([@words.val_eq_0()])),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@class.de_morgan_thm()]))),
      split_conjs(),
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
}
