///|
fn prove_tlsf_free_focus() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let geom = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(active : \{w}))"
  let _ = lemma(
    "tlsf_free_member",
    "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ active : \{w}, ∀ x : \{w}, \{geom} && MEM(x,xs) → tlsf_block_ok(val(x),lim,x,hd) && lim <= 4294967296",
    seq([
      gen,
      rw([thm("tlsf_free_geom_facts")]),
      strip,
      arw([]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_layout_members"), [
          "(xs : \{lw})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
          "(x : \{w})",
        ]),
      ),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_free_last",
    "∀ ys : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, tlsf_free_geom(d,lim,top,APPEND(ys,[m]),hd,m) → top == m && tlsf_last(hd(m))",
    seq([
      gen,
      rw([thm("tlsf_free_geom")]),
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_focus_last"), [
          "(ys : \{lw})",
          "(m : \{w})",
          "(d : \{w})",
          "(lim : Num)",
          "(top : \{w})",
          "tlsf_mark((hd : \{ht}),(m : \{w}))",
        ]),
      ),
      arw([thm("tlsf_free_mark_fields")]),
    ]),
  )
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),CONS((n : \{w}),(zs : \{lw}))))"
  let _ = lemma(
    "tlsf_free_next_geometry",
    "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ m : \{w}, ∀ n : \{w}, tlsf_free_geom(d,lim,top,\{xs},hd,m) → !tlsf_last(hd(m)) && n == word_add(word_add(m,tlsf_size(hd(m))),word(8)) && !(m == n) && tlsf_block_ok(val(n),lim,n,hd)",
    seq([
      gen,
      rw([thm("tlsf_free_geom_facts")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_free_pair_facts"), [
          "(ys : \{lw})",
          "(zs : \{lw})",
          "(m : \{w})",
          "(n : \{w})",
          "(word(0) : \{w})",
          "tlsf_origin((d : \{w}))",
          "(lim : Num)",
          "(top : \{w})",
          "(hd : \{ht})",
        ]),
      ),
      arw([]),
      strip,
      arw([]),
      @tactics.match_mp_tac(thm("tlsf_free_successor")),
      arw([]),
    ]),
  )
}
