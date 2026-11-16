// Functional updates for a returned block. Cached blocks remain allocated
// to their page; only one live block moves onto its page-local free list.

///|
fn define_tlsf_block_free_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  def(
    "tlsf_small_put",
    "tlsf_small_put((ff : (\{w}) -> \{lw}),(p : \{w}),(vs : \{lw})) == ((q : \{w}) => if q == p { vs } else { ff(q) })",
  )
  def(
    "tlsf_small_put_class",
    "tlsf_small_put_class((ff : (Num) -> \{lw}),(j : Num),(vs : \{lw})) == ((k : Num) => if k == j { vs } else { ff(k) })",
  )
  def(
    "tlsf_small_remove",
    "tlsf_small_remove((p : \{w}),(xs : \{lw})) == FILTER((q : \{w}) => !(q == p),xs)",
  )
  def(
    "tlsf_block_free_loc",
    "tlsf_block_free_loc((loc : (\{w}) -> \{lw}),(p : \{w}),(b : \{w})) == tlsf_small_put(loc,p,CONS(b,loc(p)))",
  )
  def(
    "tlsf_block_free_live",
    "tlsf_block_free_live((live : (\{w}) -> \{lw}),(p : \{w}),(b : \{w})) == tlsf_small_put(live,p,tlsf_small_remove(b,live(p)))",
  )
  let used = "tlsf_small_used((cached : (\{w}) -> \{lw})(p),(live : (\{w}) -> \{lw})(p))"
  let size = "(sz : (\{w}) -> Num)(p)"
  let cls = "DIV(\{size},8)"
  def(
    "tlsf_block_free_partial",
    "tlsf_block_free_partial((partial : (Num) -> \{lw}),(sz : (\{w}) -> Num),(cached : (\{w}) -> \{lw}),(live : (\{w}) -> \{lw}),(p : \{w})) == (if \{used} == tlsf_small_total(\{size}) { tlsf_small_put_class(partial,\{cls},CONS(p,partial(\{cls}))) } else { if \{used} == 1 { tlsf_small_put_class(partial,\{cls},tlsf_small_remove(p,partial(\{cls}))) } else { partial } })",
  )
  def(
    "tlsf_block_free_pages",
    "tlsf_block_free_pages((ps : \{lw}),(cached : (\{w}) -> \{lw}),(live : (\{w}) -> \{lw}),(p : \{w})) == (if \{used} == 1 { tlsf_small_remove(p,ps) } else { ps })",
  )
}

///|
fn prove_tlsf_block_free_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_small_remove_member",
    "∀ p : \{w}, ∀ xs : \{lw}, ∀ q : \{w}, MEM(q,tlsf_small_remove(p,xs)) == (MEM(q,xs) && !(q == p))",
    seq([
      rw([thm("tlsf_small_remove"), @lists.mem_filter()]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_remove_nil",
    "∀ p : \{w}, tlsf_small_remove(p,(NIL : \{lw})) == NIL",
    rw([thm("tlsf_small_remove"), @lists.filter()]),
  )
  let _ = lemma(
    "tlsf_small_remove_cons",
    "∀ p : \{w}, ∀ h : \{w}, ∀ t : \{lw}, tlsf_small_remove(p,CONS(h,t)) == (if h == p { tlsf_small_remove(p,t) } else { CONS(h,tlsf_small_remove(p,t)) })",
    seq([
      gen,
      rw([thm("tlsf_small_remove"), @lists.filter()]),
      @class.cond_cases_tac,
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_small_remove_absent",
    "∀ xs : \{lw}, ∀ p : \{w}, !MEM(p,xs) → tlsf_small_remove(p,xs) == xs",
    seq([
      @lists.list_induct_tac,
      rw([
        thm("tlsf_small_remove_nil"),
        thm("tlsf_small_remove_cons"),
        @lists.mem(),
      ]),
      gen,
      strip,
      free_have(
        "!((h : \{w}) == (p : \{w})) && !MEM(p,(t : \{lw}))",
        small_meson(ths([])),
      ),
      @tactics.mp_tac(
        @bool.spec(
          tm("(p : " + w + ")"),
          @kernel.assume_rule(
            tm(
              "∀ p : " +
              w +
              ", !MEM(p,(t : " +
              lw +
              ")) → tlsf_small_remove(p,t) == t",
            ),
          ),
        ),
      ),
      arw([]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_remove_split",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ p : \{w}, !MEM(p,a) && !MEM(p,z) → tlsf_small_remove(p,APPEND(a,CONS(p,z))) == APPEND(a,z)",
    seq([
      gen,
      strip,
      rw([thm("tlsf_small_remove"), @lists.filter_append(), @lists.filter()]),
      @tactics.mp_tac(
        inst(thm("tlsf_small_remove_absent"), [
          "(a : " + lw + ")",
          "(p : " + w + ")",
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_remove_absent"), [
          "(z : " + lw + ")",
          "(p : " + w + ")",
        ]),
      ),
      arw([thm("tlsf_small_remove")]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_count_one_split",
    "∀ a : \{lw}, ∀ z : \{lw}, ∀ p : \{w}, tlsf_count(p,APPEND(a,CONS(p,z))) == 1 → !MEM(p,a) && !MEM(p,z)",
    seq([
      gen,
      rw([
        thm("tlsf_small_count_append"),
        thm("tlsf_small_count_cons"),
        @equal.gsym(thm("tlsf_count_zero")),
      ]),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_release_partition",
    "∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ a : \{lw}, ∀ z : \{lw}, tlsf_small_partition(p,s,loc,cached,APPEND(a,CONS(b,z))) → tlsf_small_partition(p,s,CONS(b,loc),cached,APPEND(a,z))",
    seq([
      gen,
      rw([
        thm("tlsf_small_partition"),
        thm("tlsf_small_used"),
        thm("tlsf_small_count_append"),
        thm("tlsf_small_count_cons"),
        @lists.length_append(),
        @lists.length(),
      ]),
      strip,
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              gen,
              @tactics.first_x_assum(th => {
                @tactics.mp_tac(@bool.spec(tm("(b' : " + w + ")"), th))
              }),
              @int.arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_small_release_used",
    "∀ cached : \{lw}, ∀ a : \{lw}, ∀ z : \{lw}, ∀ b : \{w}, tlsf_small_used(cached,APPEND(a,CONS(b,z))) == SUC(tlsf_small_used(cached,APPEND(a,z)))",
    seq([
      rw([thm("tlsf_small_used"), @lists.length_append(), @lists.length()]),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_last_live",
    "∀ cached : \{lw}, ∀ a : \{lw}, ∀ z : \{lw}, ∀ b : \{w}, tlsf_small_used(cached,APPEND(a,CONS(b,z))) == 1 → cached == NIL && a == NIL && z == NIL",
    seq([
      rw([
        thm("tlsf_small_used"),
        @lists.length_append(),
        @lists.length(),
        @equal.gsym(@lists.length_eq_nil()),
      ]),
      @int.arith_tac,
    ]),
  )
}

///|
fn prove_tlsf_block_free_counts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _ = lemma(
    "tlsf_small_remove_count",
    "∀ xs : \{lw}, ∀ p : \{w}, ∀ q : \{w}, tlsf_count(q,tlsf_small_remove(p,xs)) == (if q == p { 0 } else { tlsf_count(q,xs) })",
    @tactics.thenl(
      @lists.list_induct_tac,
      @list.List([
        rw([
          thm("tlsf_small_remove_nil"),
          thm("tlsf_count"),
          @lists.filter(),
          @lists.length(),
          @class.cond_id(),
        ]),
        seq([
          gen,
          rw([thm("tlsf_small_remove_cons")]),
          @tactics.repeat_tac(@class.cond_cases_tac),
          subst_vars(),
          arw([
            thm("tlsf_small_count_cons"),
            @arith.add_clauses(),
            @theorems.eq_sym_eq(),
          ]),
        ]),
      ]),
    ),
  )
  let _ = lemma(
    "tlsf_small_member_split",
    "∀ p : \{w}, ∀ xs : \{lw}, MEM(p,xs) → (∃ a : \{lw}, ∃ z : \{lw}, xs == APPEND(a,CONS(p,z)))",
    seq([
      @tactics.gen_tac,
      @lists.list_induct_tac,
      rw([@lists.mem()]),
      gen,
      @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.exists_tac(tm("(NIL : " + lw + ")")),
              @tactics.exists_tac(tm("(t : " + lw + ")")),
              arw([@lists.append()]),
            ]),
          ),
          solve(
            seq([
              @tactics.first_x_assum(th => {
                if @basics.is_imp(@kernel.concl(th)) {
                  @tactics.mp_tac(th)
                } else {
                  @tactics.no_tac
                }
              }),
              arw([]),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              @tactics.exists_tac(tm("CONS((h : " + w + "),(a : " + lw + "))")),
              @tactics.exists_tac(tm("(z : " + lw + ")")),
              arw([@lists.append()]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
