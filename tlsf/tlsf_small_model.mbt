// Small allocations live inside used TLSF memories. A cached slot still
// contributes to Page.used; only page-local free slots can be reclaimed.
// Addresses are words, but all bounds and byte endpoints are natural numbers.

// Bounded local search keeps a failed alternative from dominating replay.

///|
fn small_meson(ts : @list.List[@kernel.Thm]) -> @tactics.Tactic raise {
  @meson.gen_meson_tac(0L, 12L, 1L, ts)
}

///|
fn define_tlsf_small_addresses() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  def("tlsf_small_total", "tlsf_small_total((s : Num)) == DIV(1056,8+s)")
  def(
    "tlsf_small_slot",
    "tlsf_small_slot((p : \{w}),(s : Num),(i : Num)) == (word(val(p)+32+(8+s)*i) : \{w})",
  )
  def(
    "tlsf_small_slots",
    "tlsf_small_slots((p : \{w}),(s : Num),0) == (NIL : \{lw}) && tlsf_small_slots(p,s,SUC(n)) == APPEND(tlsf_small_slots(p,s,n),[tlsf_small_slot(p,s,n)])",
  )
  def(
    "tlsf_small_used",
    "tlsf_small_used((cached : \{lw}),(live : \{lw})) == LENGTH(cached)+LENGTH(live)",
  )
}

///|
fn define_tlsf_small_model() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  def(
    "tlsf_small_partition",
    "tlsf_small_partition((p : \{w}),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) == ((∀ b : \{w}, tlsf_count(b,APPEND(loc,APPEND(cached,live))) == (if MEM(b,tlsf_small_slots(p,s,tlsf_small_total(s))) { 1 } else { 0 })) && LENGTH(loc)+tlsf_small_used(cached,live) == tlsf_small_total(s))",
  )
  def(
    "tlsf_small_page_ok",
    "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) == (!(p == word(0)) && MOD(val(p),8) == 0 && lim <= 4294967296 && val(p)+8+cap <= lim && 1080 <= cap && 8 <= s && s <= 256 && MOD(s,8) == 0 && tlsf_small_partition(p,s,loc,cached,live))",
  )
}

///|
fn define_tlsf_small_lists() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let lists = "(\{w}) -> \{lw}"
  let ps = "(ps : \{lw})"
  let sz = "(sz : (\{w}) -> Num)"
  let lo = "(loc : \{lists})"
  let ca = "(cached : \{lists})"
  let li = "(live : \{lists})"
  let fast = "(fast : (Num) -> \{lw})"
  let part = "(partial : (Num) -> \{lw})"
  let used = "tlsf_small_used(\{ca}(p),\{li}(p))"
  let classp = "DIV(\{sz}(p),8)"
  def(
    "tlsf_small_lists_ok",
    "tlsf_small_lists_ok(\{ps},\{sz},\{lo},\{ca},\{li},\{fast},\{part}) == ((∀ p : \{w}, MEM(p,ps) → tlsf_count(p,ps) == 1 && 0 < \{used} && (∀ b : \{w}, MEM(b,cached(p)) → tlsf_count(b,fast(\{classp})) == 1) && (\{used} < tlsf_small_total(sz(p)) → tlsf_count(p,partial(\{classp})) == 1)) && (∀ j : Num, ∀ b : \{w}, j < 33 && MEM(b,fast(j)) → (∃ p : \{w}, MEM(p,ps) && sz(p) == 8*j && MEM(b,cached(p)))) && (∀ j : Num, ∀ p : \{w}, j < 33 && MEM(p,partial(j)) → MEM(p,ps) && sz(p) == 8*j && 0 < \{used} && \{used} < tlsf_small_total(sz(p))))",
  )
  let hd = "(hd : (\{w}) -> \{w})"
  def(
    "tlsf_small_backing",
    "tlsf_small_backing((xs : \{lw}),\{hd},\{ps},\{sz},\{lo},\{ca},\{li},(lim : Num)) == (∀ p : \{w}, MEM(p,ps) → MEM(p,xs) && tlsf_used(hd(p)) && tlsf_small_page_ok(lim,p,val(tlsf_size(hd(p))),sz(p),loc(p),cached(p),live(p)))",
  )
}

///|
fn prove_tlsf_small_counts() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let w = w32
  let lw = "List[\{w}]"
  let _ = lemma(
    "tlsf_small_count_cons",
    "∀ b : \{w}, ∀ a : \{w}, ∀ xs : \{lw}, tlsf_count(b,CONS(a,xs)) == (if a == b { 1 } else { 0 })+tlsf_count(b,xs)",
    seq([
      gen,
      rw([thm("tlsf_count"), @lists.filter(), @lists.length()]),
      @class.cond_cases_tac,
      rw([@lists.length(), @arith.add_clauses()]),
      @int.arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_count_append",
    "∀ b : \{w}, ∀ xs : \{lw}, ∀ ys : \{lw}, tlsf_count(b,APPEND(xs,ys)) == tlsf_count(b,xs)+tlsf_count(b,ys)",
    rw([thm("tlsf_count"), @lists.filter_append(), @lists.length_append()]),
  )
  let sums = [
    thm("tlsf_small_partition"),
    thm("tlsf_small_used"),
    thm("tlsf_small_count_cons"),
    thm("tlsf_small_count_append"),
    @lists.length(),
    @arith.add_clauses(),
  ]
  let _ = lemma(
    "tlsf_small_partition_checkout",
    "∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, tlsf_small_partition(p,s,loc,CONS(b,cached),live) → tlsf_small_partition(p,s,loc,cached,CONS(b,live))",
    seq([
      gen,
      rw(sums),
      strip,
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(slot : \{w})")),
              @tactics.first_x_assum(th => {
                @tactics.mp_tac(@bool.spec(tm("(slot : \{w})"), th))
              }),
              @int.arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_small_partition_release",
    "∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, tlsf_small_partition(p,s,loc,cached,CONS(b,live)) → tlsf_small_partition(p,s,CONS(b,loc),cached,live)",
    seq([
      gen,
      rw(sums),
      strip,
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(slot : \{w})")),
              @tactics.first_x_assum(th => {
                @tactics.mp_tac(@bool.spec(tm("(slot : \{w})"), th))
              }),
              @int.arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_small_partition_export",
    "∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, ∀ loc : \{lw}, ∀ live : \{lw}, tlsf_small_partition(p,s,CONS(b,loc),NIL,live) → tlsf_small_partition(p,s,NIL,loc,CONS(b,live))",
    seq([
      gen,
      rw(sums),
      strip,
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(slot : \{w})")),
              @tactics.first_x_assum(th => {
                @tactics.mp_tac(@bool.spec(tm("(slot : \{w})"), th))
              }),
              @int.arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_small_accounting",
    "∀ p : \{w}, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, tlsf_small_partition(p,s,loc,cached,live) → tlsf_small_used(cached,live) <= tlsf_small_total(s) && ((tlsf_small_used(cached,live) < tlsf_small_total(s)) == !(loc == NIL))",
    seq([
      gen,
      rw([thm("tlsf_small_partition"), @equal.gsym(@lists.length_eq_nil())]),
      strip,
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_small_reclaimable",
    "∀ cached : \{lw}, ∀ live : \{lw}, (tlsf_small_used(cached,live) == 0) == (cached == NIL && live == NIL)",
    seq([
      rw([thm("tlsf_small_used"), @equal.gsym(@lists.length_eq_nil())]),
      @int.arith_tac,
    ]),
  )
}
