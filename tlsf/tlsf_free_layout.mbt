// Contract two adjacent physical blocks. Header values outside the two
// addresses are unchanged; the right block's last flag becomes the left's.

///|
fn prove_tlsf_free_layout() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_layout_prev",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ q : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, !(xs == NIL) → (tlsf_layout(p,a,lim,top,xs,hd) == tlsf_layout(q,a,lim,top,xs,hd))",
    seq([
      gen,
      @tactics.strip_assume_tac(inst(@lists.list_cases(), ["(xs : \{lw})"])),
      subst_vars(),
      rw([thm("tlsf_layout"), @lists.not_cons_nil()]),
    ]),
  )
  let vars = "∀ zs : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ lim : Num, ∀ top : \{w}, ∀ m : \{w}, ∀ r : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}"
  let sm = "val(tlsf_size((hd : \{ht})((m : \{w}))))"
  let sr = "val(tlsf_size((hd : \{ht})((r : \{w}))))"
  let sn = "val(tlsf_size((nh : \{ht})((m : \{w}))))"
  let nt = "(if (zs : \{lw}) == NIL { (m : \{w}) } else { (top : \{w}) })"
  let ag = "∀ x : \{w}, MEM(x,(zs : \{lw})) → (hd : \{ht})(x) == (nh : \{ht})(x)"
  let fields = "\{sn} == \{sm}+8+\{sr} && MOD(\{sn},8) == 0 && (tlsf_last((nh : \{ht})((m : \{w}))) == tlsf_last((hd : \{ht})((r : \{w}))))"
  let _ = lemma(
    "tlsf_layout_contract_head",
    "\{vars}, tlsf_layout(p,a,lim,top,CONS(m,CONS(r,zs)),hd) && \{fields} && (\{ag}) → tlsf_layout(p,a,lim,\{nt},CONS(m,zs),nh)",
    seq([
      gen,
      rw([thm("tlsf_layout")]),
      strip,
      free_have(
        "val((m : \{w})) == (a : Num) && !(m == word(0)) && MOD(a,8) == 0 && 16 <= \{sm} && val((r : \{w})) == a+8+\{sm} && 16 <= \{sr} && a+8+\{sm}+8+\{sr} <= (lim : Num)",
        seq([
          @tactics.undisch_tac(
            tm("tlsf_block_ok((a : Num),(lim : Num),(m : \{w}),(hd : \{ht}))"),
          ),
          @tactics.undisch_tac(
            tm(
              "tlsf_block_ok((a : Num)+8+\{sm},(lim : Num),(r : \{w}),(hd : \{ht}))",
            ),
          ),
          rw([thm("tlsf_block_ok")]),
          strip,
          strip,
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      split_conjs(),
      free_have("(a : Num)+8+\{sn} == a+8+\{sm}+8+\{sr}", @int.asm_arith_tac),
      free_have(
        "tlsf_layout((r : \{w}),(a : Num)+8+\{sn},(lim : Num),(top : \{w}),(zs : \{lw}),(nh : \{ht}))",
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_layout_cong"), [
              "(zs : \{lw})",
              "(r : \{w})",
              "(a : Num)+8+\{sn}",
              "(lim : Num)",
              "(top : \{w})",
              "(hd : \{ht})",
              "(nh : \{ht})",
            ]),
          ),
          arw([]),
        ]),
      ),
      @tactics.strip_assume_tac(inst(@lists.list_cases(), ["(zs : \{lw})"])),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(
          ths([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]),
        ),
      ),
      split_conjs(),
      rw([thm("tlsf_layout"), thm("tlsf_block_ok"), @lists.not_cons_nil()]),
      use_eqs(t => @basics.is_eq(t)),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@arith.add_assoc()]))),
      arw([
        thm("tlsf_layout"),
        thm("tlsf_block_ok"),
        @lists.not_cons_nil(),
        @arith.add_assoc(),
      ]),
      @int.asm_arith_tac,
    ]),
  )
  let old = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS((r : \{w}),(zs : \{lw}))))"
  let nx = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let _ = lemma(
    "tlsf_layout_contract",
    "∀ ys : \{lw}, \{vars}, tlsf_layout(p,a,lim,top,\{old},hd) && \{fields} && (∀ x : \{w}, MEM(x,APPEND(ys,zs)) → hd(x) == nh(x)) → tlsf_layout(p,a,lim,\{nt},\{nx},nh)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_cut_at"), [
          "(ys : \{lw})",
          "CONS((r : \{w}),(zs : \{lw}))",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      free_have(
        "tlsf_layout(tlsf_end((p : \{w}),(ys : \{lw})),val((m : \{w})),(lim : Num),\{nt},CONS(m,(zs : \{lw})),(nh : \{ht}))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_contract_head"), [
              "(zs : \{lw})",
              "tlsf_end((p : \{w}),(ys : \{lw}))",
              "val((m : \{w}))",
              "(lim : Num)",
              "(top : \{w})",
              "(m : \{w})",
              "(r : \{w})",
              "(hd : \{ht})",
              "(nh : \{ht})",
            ]),
          ),
          arw([]),
          @meson.asm_meson_tac(ths([@lists.mem_append()])),
        ]),
      ),
      @tactics.match_mp_tac(
        inst(thm("tlsf_layout_glue"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "val((m : \{w}))",
          "(lim : Num)",
          nt,
          "(hd : \{ht})",
          "(nh : \{ht})",
        ]),
      ),
      arw([]),
      @meson.asm_meson_tac(ths([@lists.mem_append()])),
    ]),
  )
}
