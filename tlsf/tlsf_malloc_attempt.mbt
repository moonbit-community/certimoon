// Exhaust the dispatch choices using facts derived from the combined invariant.

///|
fn malloc_list_cases(
  list : String,
  hd : String,
  tl : String,
) -> @tactics.Tactic raise {
  seq([
    @tactics.mp_tac(@bool.ispec(tm(list), @lists.list_cases())),
    @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
    @tactics.try_tac(
      @tactics.first_x_assum(th => {
        if @basics.is_exists(@kernel.concl(th)) {
          @tactics.x_choose_then(tm(hd))(
            @tactics.x_choose_then(tm(tl))(th => @tactics.assume_tac(th)),
          )(th)
        } else {
          @tactics.no_tac
        }
      }),
    ),
  ])
}

///|
fn prove_tlsf_malloc_attempt_facts() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : List[" + w + "])"
  let z = "(z : List[" + w + "])"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let k = "val(" + cls + ")"
  let args = malloc_case_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let facts = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && " +
    block_lists(a)
  let cond = facts +
    " && val(" +
    n +
    ") <= 4160749568 && (" +
    malloc_helper_natives() +
    ")"
  let add = (th : @kernel.Thm) => {
    (g : @tactics.Goal) => @tactics.strip_assume_tac(block_under(th, g))(g)
  }
  for v in malloc_variant_names() {
    let q = malloc_attempt_post(v, a, n)
    let lc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let apply_case = (kind : String) => {
      seq([
        free_apply(inst(thm("tlsf_malloc_" + v + "_" + kind + "_case"), args)),
        malloc_vc(),
      ])
    }
    let _ = lemma(
      "tlsf_malloc_" + v + "_attempt_facts",
      page_quantify(malloc_case_variables()) +
      cond +
      " → sl_triple_g((G : " +
      malloc_g_variables()[0].1 +
      "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
      (if v == "try" { q } else { "(rp : " + sassn + ")" }) +
      ",st(NIL," +
      lc +
      "," +
      r +
      ")," +
      malloc_part(v, "body") +
      "," +
      q +
      ",[" +
      q +
      "])",
      () => {
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          add(inst(thm("tlsf_malloc_guard_facts"), a)),
          add(inst(thm("tlsf_malloc_initialized_guards"), a)),
          @class.asm_cases_tac(tm(n + " == word(0)")),
          @tactics.first(
            @list.List([
              solve(
                seq([
                  subst_only("n"),
                  free_apply(inst(thm("tlsf_malloc_" + v + "_zero_case"), args)),
                ]),
              ),
              solve(
                seq([
                  free_have(
                    "!(val(" + n + ") == 0)",
                    seq([arw([@words.val_eq_0()])]),
                  ),
                  free_have("0 < val(" + n + ")", @int.asm_arith_tac),
                  @class.asm_cases_tac(tm("val(" + n + ") <= 256")),
                  @tactics.first(
                    @list.List([
                      solve(
                        seq([
                          add(inst(thm("tlsf_malloc_request_setup"), [n])),
                          malloc_list_cases(a[13] + "(" + k + ")", b, bs),
                          @tactics.first(
                            @list.List([
                              solve(
                                seq([
                                  malloc_list_cases(a[14] + "(" + k + ")", p, z),
                                  @tactics.first(
                                    @list.List([
                                      solve(apply_case("fresh")),
                                      solve(
                                        seq([
                                          add(
                                            inst(
                                              thm(
                                                "tlsf_malloc_partial_dispatch",
                                              ),
                                              a + [k, p, z],
                                            ),
                                          ),
                                          free_have(
                                            "!(" + p + " == word(0))",
                                            seq([
                                              @tactics.first_x_assum(th => {
                                                if head_name(@kernel.concl(th)) ==
                                                  "tlsf_small_page_ok" {
                                                  @tactics.mp_tac(th)
                                                } else {
                                                  @tactics.no_tac
                                                }
                                              }),
                                              @simp.rewrite_tac(
                                                ths([thm("tlsf_small_page_ok")]),
                                              ),
                                              @tactics.repeat_tac(
                                                @tactics.strip_tac,
                                              ),
                                              arw([]),
                                            ]),
                                          ),
                                          apply_case("partial"),
                                        ]),
                                      ),
                                    ]),
                                  ),
                                ]),
                              ),
                              solve(
                                seq([
                                  add(
                                    inst(
                                      thm("tlsf_malloc_cached_dispatch"),
                                      a + [k, b, bs],
                                    ),
                                  ),
                                  add(
                                    inst(
                                      thm("tlsf_malloc_cached_bounds"),
                                      a + [p, b],
                                    ),
                                  ),
                                  apply_case("cached"),
                                ]),
                              ),
                            ]),
                          ),
                        ]),
                      ),
                      solve(apply_case("large")),
                    ]),
                  ),
                ]),
              ),
            ]),
          ),
        ])
      },
    )
  }
}

///|
fn prove_tlsf_malloc_attempt() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let facts = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && " +
    block_lists(a)
  let vars = malloc_case_variables()
  let args = vars.map(x => "(" + x.0 + " : " + x.1 + ")")
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  for v in malloc_variant_names() {
    let q = malloc_attempt_post(v, a, n)
    let lc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let p = "st(NIL," + lc + "," + r + ")"
    let strong = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => (" +
      facts +
      ") && (" +
      p +
      ")(vs,lc,gs,ms,h)"
    let _ = lemma(
      "tlsf_malloc_" + v + "_attempt",
      page_quantify(vars) +
      "val(" +
      n +
      ") <= 4160749568 && (" +
      malloc_helper_natives() +
      ") → sl_triple_g((G : " +
      malloc_g_variables()[0].1 +
      "),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
      (if v == "try" { q } else { "(rp : " + sassn + ")" }) +
      "," +
      p +
      "," +
      malloc_part(v, "body") +
      "," +
      q +
      ",[" +
      q +
      "])",
      () => {
        seq([
          gen,
          strip,
          @logic.match_mp_tac(thm("sl_pre_g")),
          @tactics.exists_tac(tm(strong)),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              seq([
                gen,
                @simp.rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
                strip,
                @simp.asm_rewrite_tac(ths([])),
                free_apply(
                  inst(
                    thm("tlsf_malloc_allocator_facts"),
                    a +
                    [
                      "(fp : " + rty + ")((gs : List[Value]),(lim : Num))",
                      "(h : " + heap + ")",
                    ],
                  ),
                ),
              ]),
              seq([
                @logic.match_mp_tac(thm("sl_pure_g")),
                strip,
                free_apply(
                  inst(thm("tlsf_malloc_" + v + "_attempt_facts"), args),
                ),
              ]),
            ]),
          ),
        ])
      },
    )
  }
}
