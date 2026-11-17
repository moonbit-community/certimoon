// A full target page replaces its local list with cached slots and one live
// slot. Removing it from partial lists does not change any other owner.

///|
fn page_publish_atomic(ts : Array[@kernel.Thm]) -> @tactics.Tactic {
  g => {
    @meson.gen_meson_tac(
      0L,
      6L,
      1L,
      ths(
        g.0
        .to_array()
        .filter(t => !@basics.is_forall(@kernel.concl(t.1)))
        .map(t => t.1) +
        ts,
      ),
    )(g)
  }
}

///|
fn page_publish_old_page_facts(q : String) -> @tactics.Tactic {
  @tactics.first_assum(th => {
    if !@basics.is_forall(@kernel.concl(th)) {
      return @tactics.no_tac
    }
    let spec = @bool.spec(tm(q), th) catch { _ => return @tactics.no_tac }
    let c = @kernel.concl(spec)
    if !@basics.is_imp(c) {
      return @tactics.no_tac
    }
    let (p, r) = @basics.dest_imp(c)
    if head_name(p) != "MEM" || !@basics.is_conj(r) {
      return @tactics.no_tac
    }
    if head_name(@equal.lhs(@basics.dest_conj(r).0)) != "tlsf_count" {
      return @tactics.no_tac
    }
    g => @tactics.strip_assume_tac(block_under(spec, g))(g)
  })
}

///|
fn prove_tlsf_page_publish_lists() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let vs = [
    ("ps", lw),
    ("sz", "(" + w + ") -> Num"),
    ("loc", "(" + w + ") -> " + lw),
    ("cached", "(" + w + ") -> " + lw),
    ("live", "(" + w + ") -> " + lw),
    ("fast", "(Num) -> " + lw),
    ("partial", "(Num) -> " + lw),
  ]
  let av = vs.map(v => "(" + v.0 + " : " + v.1 + ")")
  let nv = vs.map(v => (v.0 + "2", v.1))
  let na = nv.map(v => "(" + v.0 + " : " + v.1 + ")")
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => {
    (g : @tactics.Goal) => {
      @simp.rewrite_tac(
        ths(
          g.0
          .to_array()
          .filter(t => {
            !@basics.is_forall(@kernel.concl(t.1)) &&
            !(@basics.is_eq(@kernel.concl(t.1)) &&
            @equal.lhs(@kernel.concl(t.1)) is Var("s", _))
          })
          .map(t => t.1) +
          ts,
        ),
      )(g)
    }
  }
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let same = "∀ q : " +
    w +
    ", !(q == (p : " +
    w +
    ")) → (MEM(q,ps2) == MEM(q,ps)) && tlsf_count(q,ps2) == tlsf_count(q,ps) && sz2(q) == sz(q) && cached2(q) == cached(q) && live2(q) == live(q)"
  let other = (q : String) => {
    "(MEM(" +
    q +
    ",(ps2 : " +
    lw +
    ")) == MEM(" +
    q +
    ",(ps : " +
    lw +
    "))) && tlsf_count(" +
    q +
    ",ps2) == tlsf_count(" +
    q +
    ",ps) && (sz2 : (" +
    w +
    ") -> Num)(" +
    q +
    ") == (sz : (" +
    w +
    ") -> Num)(" +
    q +
    ") && (cached2 : (" +
    w +
    ") -> " +
    lw +
    ")(" +
    q +
    ") == (cached : (" +
    w +
    ") -> " +
    lw +
    ")(" +
    q +
    ") && (live2 : (" +
    w +
    ") -> " +
    lw +
    ")(" +
    q +
    ") == (live : (" +
    w +
    ") -> " +
    lw +
    ")(" +
    q +
    ")"
  }
  let old = "tlsf_small_lists_ok(" + av.join(",") + ")"
  let newer = "tlsf_small_lists_ok(" + na.join(",") + ")"
  let cond = old +
    " && (∀ q : " +
    w +
    ", MEM(q,ps) → DIV(sz(q),8) < 33) && (" +
    same +
    ") && MEM((p : " +
    w +
    "),ps2) && tlsf_count(p,ps2) == 1 && sz2(p) == (s : Num) && (cached2 : (" +
    w +
    ") -> " +
    lw +
    ")(p) == (bs : " +
    lw +
    ") && tlsf_small_used(cached2(p),live2(p)) == tlsf_small_total(s) && 0 < tlsf_small_total(s) && s == 8*(k : Num) && k < 33 && (!MEM(p,ps) || cached(p) == NIL) && fast(k) == NIL && fast2 == tlsf_small_put_class(fast,k,bs) && (∀ b : " +
    w +
    ", MEM(b,bs) → tlsf_count(b,bs) == 1) && (∀ j : Num, j < 33 → partial2(j) == tlsf_small_remove(p,partial(j)))"
  let _ = lemma(
    "tlsf_page_publish_lists",
    page_quantify(vs + nv + [("p", w), ("s", "Num"), ("bs", lw), ("k", "Num")]) +
    cond +
    " → " +
    newer,
    seq([
      gen,
      strip,
      free_have(
        "DIV((s : Num),8) == (k : Num)",
        seq([
          @tactics.match_mp_tac(
            inst(@arith.div_uniq(), ["(s : Num)", "8", "(k : Num)", "0"]),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.undisch_tac(tm(old)),
      rw([thm("tlsf_small_lists_ok")]),
      strip,
      rw([thm("tlsf_small_lists_ok")]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.x_gen_tac(tm("(q : " + w + ")")),
            @tactics.disch_tac,
            @tactics.thenl(
              @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
              @list.List([
                seq([
                  subst_only("q"),
                  arw([@arith.lt_refl(), thm("tlsf_small_put_class")]),
                  @tactics.first_assum(th => @tactics.accept_tac(th)),
                ]),
                seq([
                  free_have(
                    other("(q : " + w + ")"),
                    seq([
                      @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                      arw([]),
                    ]),
                  ),
                  split_conjs(),
                  arw([]),
                  free_have(
                    "MEM((q : " + w + "),(ps : " + lw + "))",
                    page_publish_atomic([]),
                  ),
                  page_publish_old_page_facts("(q : " + w + ")"),
                  free_have(
                    "tlsf_count((q : " +
                    w +
                    "),(ps : " +
                    lw +
                    ")) == 1 && 0 < tlsf_small_used((cached : (" +
                    w +
                    ") -> " +
                    lw +
                    ")(q),(live : (" +
                    w +
                    ") -> " +
                    lw +
                    ")(q))",
                    arw([]),
                  ),
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @tactics.first(
                    @list.List([
                      solve(arw([])),
                      solve(
                        seq([
                          @tactics.x_gen_tac(tm("(a : " + w + ")")),
                          strip,
                          free_have(
                            "tlsf_count((a : " +
                            w +
                            "),(fast : (Num) -> " +
                            lw +
                            ")(DIV((sz : (" +
                            w +
                            ") -> Num)((q : " +
                            w +
                            ")),8))) == 1",
                            seq([
                              @tactics.first_assum(th => {
                                @tactics.match_mp_tac(th)
                              }),
                              arw([]),
                            ]),
                          ),
                          @tactics.thenl(
                            @class.asm_cases_tac(
                              tm(
                                "DIV((sz : (" +
                                w +
                                ") -> Num)((q : " +
                                w +
                                ")),8) == (k : Num)",
                              ),
                            ),
                            @list.List([
                              seq([
                                @tactics.mp_tac(
                                  @kernel.assume_rule(
                                    tm(
                                      "tlsf_count((a : " +
                                      w +
                                      "),(fast : (Num) -> " +
                                      lw +
                                      ")(DIV((sz : (" +
                                      w +
                                      ") -> Num)((q : " +
                                      w +
                                      ")),8))) == 1",
                                    ),
                                  ),
                                ),
                                rw([
                                  @kernel.assume_rule(
                                    tm(
                                      "DIV((sz : (" +
                                      w +
                                      ") -> Num)((q : " +
                                      w +
                                      ")),8) == (k : Num)",
                                    ),
                                  ),
                                  @kernel.assume_rule(
                                    tm(
                                      "(fast : (Num) -> " +
                                      lw +
                                      ")((k : Num)) == NIL",
                                    ),
                                  ),
                                  thm("tlsf_small_count_nil"),
                                ]),
                                @tactics.conv_tac(@calc_num.num_reduce_conv),
                              ]),
                              seq([arw([thm("tlsf_small_put_class")])]),
                            ]),
                          ),
                        ]),
                      ),
                      solve(
                        seq([
                          strip,
                          free_have(
                            "DIV((sz : (" +
                            w +
                            ") -> Num)((q : " +
                            w +
                            ")),8) < 33",
                            seq([
                              @tactics.first_assum(th => {
                                @tactics.match_mp_tac(th)
                              }),
                              arw([]),
                            ]),
                          ),
                          free_have(
                            "(partial2 : (Num) -> " +
                            lw +
                            ")(DIV((sz : (" +
                            w +
                            ") -> Num)((q : " +
                            w +
                            ")),8)) == tlsf_small_remove((p : " +
                            w +
                            "),(partial : (Num) -> " +
                            lw +
                            ")(DIV(sz(q),8)))",
                            seq([
                              @tactics.first_assum(th => {
                                @tactics.match_mp_tac(th)
                              }),
                              arw([]),
                            ]),
                          ),
                          arw([thm("tlsf_small_remove_count")]),
                          @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                    ]),
                  ),
                ]),
              ]),
            ),
          ]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              seq([
                @tactics.x_gen_tac(tm("(j : Num)")),
                @tactics.x_gen_tac(tm("(a : " + w + ")")),
                strip,
                @tactics.thenl(
                  @class.asm_cases_tac(tm("(j : Num) == (k : Num)")),
                  @list.List([
                    seq([
                      subst_only("j"),
                      free_have(
                        "MEM((a : " + w + "),(bs : " + lw + "))",
                        seq([
                          @tactics.undisch_tac(
                            tm(
                              "MEM((a : " +
                              w +
                              "),(fast2 : (Num) -> " +
                              lw +
                              ")((k : Num)))",
                            ),
                          ),
                          arw([thm("tlsf_small_put_class")]),
                        ]),
                      ),
                      @tactics.exists_tac(tm("(p : " + w + ")")),
                      arw([thm("tlsf_small_put_class")]),
                      @tactics.first_assum(th => @tactics.accept_tac(th)),
                    ]),
                    seq([
                      free_have(
                        "MEM((a : " +
                        w +
                        "),(fast : (Num) -> " +
                        lw +
                        ")((j : Num)))",
                        seq([
                          @tactics.undisch_tac(
                            tm(
                              "MEM((a : " +
                              w +
                              "),(fast2 : (Num) -> " +
                              lw +
                              ")((j : Num)))",
                            ),
                          ),
                          arw([thm("tlsf_small_put_class")]),
                        ]),
                      ),
                      free_have(
                        "∃ owner : " +
                        w +
                        ", MEM(owner,(ps : " +
                        lw +
                        ")) && (sz : (" +
                        w +
                        ") -> Num)(owner) == 8*(j : Num) && MEM((a : " +
                        w +
                        "),(cached : (" +
                        w +
                        ") -> " +
                        lw +
                        ")(owner))",
                        seq([
                          @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                      @tactics.first_x_assum(th => {
                        if @basics.is_exists(@kernel.concl(th)) {
                          @tactics.x_choose_then(tm("(owner : " + w + ")"))(th => {
                            @tactics.strip_assume_tac(th)
                          })(th)
                        } else {
                          @tactics.no_tac
                        }
                      }),
                      free_have(
                        "!((owner : " + w + ") == (p : " + w + "))",
                        page_publish_atomic([@lists.mem()]),
                      ),
                      free_have(
                        other("(owner : " + w + ")"),
                        seq([
                          @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                      split_conjs(),
                      @tactics.exists_tac(tm("(owner : " + w + ")")),
                      arw([]),
                    ]),
                  ]),
                ),
              ]),
              seq([
                @tactics.x_gen_tac(tm("(j : Num)")),
                @tactics.x_gen_tac(tm("(q : " + w + ")")),
                strip,
                free_have(
                  "(partial2 : (Num) -> " +
                  lw +
                  ")((j : Num)) == tlsf_small_remove((p : " +
                  w +
                  "),(partial : (Num) -> " +
                  lw +
                  ")(j))",
                  seq([
                    @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                    arw([]),
                  ]),
                ),
                free_have(
                  "MEM((q : " +
                  w +
                  "),(partial : (Num) -> " +
                  lw +
                  ")((j : Num))) && !(q == (p : " +
                  w +
                  "))",
                  seq([
                    @tactics.undisch_tac(
                      tm(
                        "MEM((q : " +
                        w +
                        "),(partial2 : (Num) -> " +
                        lw +
                        ")((j : Num)))",
                      ),
                    ),
                    arw([thm("tlsf_small_remove_member")]),
                  ]),
                ),
                free_have(
                  other("(q : " + w + ")"),
                  seq([
                    @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                    arw([]),
                  ]),
                ),
                split_conjs(),
                arw([]),
                small_meson(ths([])),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
