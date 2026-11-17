///|
fn malloc_cached_args(
  a : Array[String],
  p : String,
  b : String,
  bs : String,
  k : String,
) -> Array[String] {
  let n = a.copy()
  n[11] = "tlsf_small_put(" +
    a[11] +
    "," +
    p +
    ",tlsf_small_remove(" +
    b +
    "," +
    a[11] +
    "(" +
    p +
    ")))"
  n[12] = "tlsf_small_put(" +
    a[12] +
    "," +
    p +
    ",CONS(" +
    b +
    "," +
    a[12] +
    "(" +
    p +
    ")))"
  n[13] = "tlsf_small_put_class(" + a[13] + "," + k + "," + bs + ")"
  n
}

///|
fn prove_tlsf_malloc_cached_member() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let _ = lemma(
    "tlsf_malloc_cached_member",
    "∀ ff : (" +
    w +
    ") -> " +
    lw +
    ", ∀ p : " +
    w +
    ", ∀ b : " +
    w +
    ", ∀ q : " +
    w +
    ", ∀ a : " +
    w +
    ", MEM(a,tlsf_small_put(ff,p,tlsf_small_remove(b,ff(p)))(q)) == (MEM(a,ff(q)) && (q == p → !(a == b)))",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(ths([thm("tlsf_small_put")])),
        @class.cond_cases_tac,
        subst_vars(),
        @simp.asm_rewrite_tac(ths([thm("tlsf_small_remove_member")])),
        @meson.meson_tac(ths([])),
      ])
    },
  )
}

///|
fn prove_tlsf_malloc_cached_lists() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let n = malloc_cached_args(a, p, b, bs, k)
  let vs = page_model_variables() +
    [("p", w), ("b", w), ("bs", lw), ("k", "Num")]
  let used = (a : Array[String], q : String) => {
    "tlsf_small_used(" + a[11] + "(" + q + ")," + a[12] + "(" + q + "))"
  }
  let sameUsed = "∀ q : " + w + ", " + used(n, "q") + " == " + used(a, "q")
  let other = "∀ q : " +
    w +
    ", MEM(q," +
    a[8] +
    ") && !(q == " +
    p +
    ") → !MEM(" +
    b +
    "," +
    a[11] +
    "(q))"
  let cond = block_lists(a) +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    b +
    "," +
    a[11] +
    "(" +
    p +
    ")) && " +
    a[9] +
    "(" +
    p +
    ") == 8*" +
    k +
    " && " +
    k +
    " < 33 && " +
    a[13] +
    "(" +
    k +
    ") == CONS(" +
    b +
    "," +
    bs +
    ") && (" +
    sameUsed +
    ") && (" +
    other +
    ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cachedCount = (q : String, x : String) => {
    "tlsf_count(" + x + "," + a[13] + "(DIV(" + a[9] + "(" + q + "),8))) == 1"
  }
  let oldOwner = (j : String, x : String) => {
    "∃ owner : " +
    w +
    ", MEM(owner," +
    a[8] +
    ") && " +
    a[9] +
    "(owner) == 8*" +
    j +
    " && MEM(" +
    x +
    "," +
    a[11] +
    "(owner))"
  }
  let chooseOwner = @tactics.first_x_assum(th => {
    if @basics.is_exists(@kernel.concl(th)) {
      @tactics.x_choose_then(tm("(owner : " + w + ")"))(th => {
        @tactics.strip_assume_tac(th)
      })(th)
    } else {
      @tactics.no_tac
    }
  })
  let _ = lemma(
    "tlsf_malloc_cached_lists",
    page_quantify(vs) + cond + " → " + block_lists(n),
    () => {
      seq([
        gen,
        strip,
        free_have(
          "DIV(" + a[9] + "(" + p + "),8) == " + k,
          seq([
            @logic.match_mp_tac(
              inst(@arith.div_uniq(), [a[9] + "(" + p + ")", "8", k, "0"]),
            ),
            @int.asm_arith_tac,
          ]),
        ),
        @tactics.undisch_tac(tm(block_lists(a))),
        rw([thm("tlsf_small_lists_ok")]),
        strip,
        page_publish_old_page_facts(p),
        free_have(
          cachedCount(p, b),
          seq([@tactics.first_assum(th => @logic.match_mp_tac(th)), arw([])]),
        ),
        free_have(
          "!MEM(" + b + "," + bs + ")",
          seq([
            @tactics.undisch_tac(tm(cachedCount(p, b))),
            arw([
              thm("tlsf_small_count_cons"),
              @equal.gsym(thm("tlsf_count_zero")),
            ]),
            @int.asm_arith_tac,
          ]),
        ),
        g => {
          let eq = @kernel.assume_rule(tm(sameUsed))
          seq([
            rw([thm("tlsf_small_lists_ok"), eq]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  @tactics.x_gen_tac(tm("(q : " + w + ")")),
                  @tactics.disch_tac,
                  page_publish_old_page_facts("(q : " + w + ")"),
                  arw([]),
                  @tactics.repeat_tac(@tactics.conj_tac),
                  @tactics.first(
                    @list.List([
                      solve(arw([])),
                      solve(
                        seq([
                          strip,
                          @tactics.first_assum(th => @logic.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                      solve(
                        seq([
                          @tactics.x_gen_tac(tm("(a : " + w + ")")),
                          strip,
                          free_have(
                            "MEM((a : " +
                            w +
                            ")," +
                            a[11] +
                            "((q : " +
                            w +
                            "))) && ((q : " +
                            w +
                            ") == " +
                            p +
                            " → !((a : " +
                            w +
                            ") == " +
                            b +
                            "))",
                            seq([
                              @tactics.undisch_tac(
                                tm(
                                  "MEM((a : " +
                                  w +
                                  ")," +
                                  n[11] +
                                  "((q : " +
                                  w +
                                  ")))",
                                ),
                              ),
                              rw([thm("tlsf_malloc_cached_member")]),
                            ]),
                          ),
                          split_conjs(),
                          free_have(
                            cachedCount("(q : " + w + ")", "(a : " + w + ")"),
                            seq([
                              @tactics.first_assum(th => @logic.match_mp_tac(th)),
                              arw([]),
                            ]),
                          ),
                          @tactics.thenl(
                            @class.asm_cases_tac(
                              tm("DIV(" + a[9] + "((q : " + w + ")),8) == " + k),
                            ),
                            @list.List([
                              seq([
                                free_have(
                                  "!((a : " + w + ") == " + b + ")",
                                  seq([
                                    @class.asm_cases_tac(
                                      tm("(q : " + w + ") == " + p),
                                    ),
                                    @tactics.first(
                                      @list.List([
                                        solve(
                                          seq([
                                            @tactics.undisch_tac(
                                              tm(
                                                "MEM((a : " +
                                                w +
                                                ")," +
                                                n[11] +
                                                "((q : " +
                                                w +
                                                ")))",
                                              ),
                                            ),
                                            arw([
                                              thm("tlsf_small_put"),
                                              thm("tlsf_small_remove_member"),
                                            ]),
                                            small_meson(ths([])),
                                          ]),
                                        ),
                                        solve(
                                          seq([
                                            free_have(
                                              "!MEM(" +
                                              b +
                                              "," +
                                              a[11] +
                                              "((q : " +
                                              w +
                                              ")))",
                                              seq([
                                                @tactics.first_assum(th => {
                                                  @logic.match_mp_tac(th)
                                                }),
                                                arw([]),
                                              ]),
                                            ),
                                            page_publish_atomic([]),
                                          ]),
                                        ),
                                      ]),
                                    ),
                                  ]),
                                ),
                                @tactics.undisch_tac(
                                  tm(
                                    cachedCount(
                                      "(q : " + w + ")",
                                      "(a : " + w + ")",
                                    ),
                                  ),
                                ),
                                arw([
                                  thm("tlsf_small_put_class"),
                                  thm("tlsf_small_count_cons"),
                                  @theorems.eq_sym_eq(),
                                  @arith.add_clauses(),
                                ]),
                              ]),
                              arw([thm("tlsf_small_put_class")]),
                            ]),
                          ),
                        ]),
                      ),
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
                      free_have(
                        "MEM((a : " + w + ")," + a[13] + "((j : Num)))",
                        seq([
                          @tactics.undisch_tac(
                            tm("MEM((a : " + w + ")," + n[13] + "((j : Num)))"),
                          ),
                          rw([thm("tlsf_small_put_class")]),
                          @class.cond_cases_tac,
                          arw([@lists.mem()]),
                          small_meson(ths([])),
                        ]),
                      ),
                      free_have(
                        oldOwner("(j : Num)", "(a : " + w + ")"),
                        seq([
                          @tactics.first_assum(th => @logic.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                      chooseOwner,
                      @tactics.exists_tac(tm("(owner : " + w + ")")),
                      @tactics.thenl(
                        @class.asm_cases_tac(tm("(j : Num) == " + k)),
                        @list.List([
                          seq([
                            free_have(
                              "!((a : " + w + ") == " + b + ")",
                              seq([
                                @tactics.undisch_tac(
                                  tm(
                                    "MEM((a : " +
                                    w +
                                    ")," +
                                    n[13] +
                                    "((j : Num)))",
                                  ),
                                ),
                                arw([thm("tlsf_small_put_class")]),
                                page_publish_atomic([]),
                              ]),
                            ),
                            rw([
                              thm("tlsf_small_put"),
                              thm("tlsf_small_remove_member"),
                            ]),
                            @class.cond_cases_tac,
                            subst_vars(),
                            arw([thm("tlsf_small_remove_member")]),
                            @tactics.try_tac(
                              @tactics.first_assum(th => @tactics.accept_tac(th)),
                            ),
                          ]),
                          seq([
                            free_have(
                              "!((owner : " + w + ") == " + p + ")",
                              seq([
                                @tactics.disch_tac,
                                subst_only("owner"),
                                @tactics.undisch_tac(
                                  tm(a[9] + "(" + p + ") == 8*(j : Num)"),
                                ),
                                arw([]),
                                @int.asm_arith_tac,
                              ]),
                            ),
                            arw([thm("tlsf_small_put")]),
                          ]),
                        ]),
                      ),
                    ]),
                    seq([
                      @tactics.x_gen_tac(tm("(j : Num)")),
                      @tactics.x_gen_tac(tm("(q : " + w + ")")),
                      strip,
                      free_have(
                        "MEM((q : " +
                        w +
                        ")," +
                        a[8] +
                        ") && " +
                        a[9] +
                        "((q : " +
                        w +
                        ")) == 8*(j : Num) && 0 < " +
                        used(a, "(q : " + w + ")") +
                        " && " +
                        used(a, "(q : " + w + ")") +
                        " < tlsf_small_total(" +
                        a[9] +
                        "((q : " +
                        w +
                        ")))",
                        seq([
                          @tactics.first_assum(th => @logic.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ),
                      arw([]),
                    ]),
                  ]),
                ),
              ]),
            ),
          ])(g)
        },
      ])
    },
  )
}
