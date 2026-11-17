// Each short-circuit branch composes a read with either the empty branch
// or the complete native-pop/merge body, and folds the working invariant.

///|
fn prove_tlsf_free_paths() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let both = (a : @tactics.Tactic, b : @tactics.Tactic) => {
    @tactics.thenl(@tactics.conj_tac, @list.List([a, b]))
  }
  let same = seq([gen, beta_goal(), strip, arw([])])
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ m0 : \{w}, ∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ qs : \{lw}, ∀ zs : \{lw}, ∀ ts : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ n : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let native = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code((d : \{w})))"
  let norm = [
    @equal.gsym(@lists.append_assoc()),
    @lists.append(),
    @lists.not_cons_nil(),
  ]
  for prev in [true, false] {
    let dir = if prev { "prev" } else { "next" }
    // boundary, used neighbour, free neighbour with/without successor
    for kind in [0, 1, 2, 3] {
      let missing = kind == 0
      let merge = kind >= 2
      let last = kind == 2
      let prefix = if prev {
        if missing {
          "(NIL : \{lw})"
        } else {
          "APPEND((qs : \{lw}),[(p : \{w})])"
        }
      } else {
        "(qs : \{lw})"
      }
      let suffix = if prev {
        if merge {
          if last {
            "(NIL : \{lw})"
          } else {
            "CONS((n : \{w}),(ts : \{lw}))"
          }
        } else {
          "(zs : \{lw})"
        }
      } else if missing {
        "(NIL : \{lw})"
      } else {
        "CONS((p : \{w})," +
        (if merge {
          if last {
            "(NIL : \{lw})"
          } else {
            "CONS((n : \{w}),(ts : \{lw}))"
          }
        } else {
          "(zs : \{lw})"
        }) +
        ")"
      }
      let xs = "APPEND(\{prefix},CONS((m : \{w}),\{suffix}))"
      let cond = "\{native} && tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht}),(m : \{w})) && !tlsf_used(hd(m)) && tlsf_bins_match(\{xs},tlsf_mark(hd,m),(bl : \{bt})) && tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),m,hd) && tlsf_free_live((xs0 : \{lw}),hd0,m0,\{xs},hd)" +
        (if prev { "" } else { " && tlsf_free_left(\{prefix},hd)" }) +
        (if missing {
          ""
        } else if merge {
          " && !tlsf_used(hd((p : \{w})))"
        } else {
          " && tlsf_used(hd((p : \{w})))"
        })
      let tst = @simp.rewrite_rule(ths(norm))(
        inst(
          thm(
            "tlsf_free_\{dir}" +
            (if missing { "_boundary_test" } else { "_neighbour_test" }),
          ),
          [
            prefix,
            "(qs : \{lw})",
            suffix,
            if prev {
              "(ts : \{lw})"
            } else if merge {
              if last {
                "(NIL : \{lw})"
              } else {
                "CONS((n : \{w}),(ts : \{lw}))"
              }
            } else {
              "(zs : \{lw})"
            },
            "(m : \{w})",
            "(p : \{w})",
            "(p : \{w})",
            "(d : \{w})",
            "(pop : Num)",
            "(push : Num)",
            "(lim : Num)",
            "(top : \{w})",
            "(hd : \{ht})",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(l1 : Value)",
            "(l2 : Value)",
            "(fp : \{rty})",
          ],
        ),
      )
      let tt = args_of(@basics.dest_imp(@kernel.concl(tst)).1, "sl_triple", 3).unwrap()
      let st1 = args_of(tt[2], "st", 3).unwrap()
      let target = "tlsf_free_work((d : \{w}),(lim : Num),(m0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fp : \{rty}),T," +
        (if prev { "F" } else { "T" }) +
        ")"
      let other_suffix = if last {
        "(NIL : \{lw})"
      } else {
        "CONS((n : \{w}),(ts : \{lw}))"
      }
      let left = if prev { "(p : \{w})" } else { "(m : \{w})" }
      let right = if prev { "(m : \{w})" } else { "(p : \{w})" }
      let hp = "(hd : \{ht})((p : \{w}))"
      let rem = "APPEND((us : \{lw}),(vs : \{lw}))"
      let nh = "tlsf_merge_headers((hd : \{ht}),\{left},\{right})"
      let fold = inst(thm("tlsf_free_work_fold"), [
        "(d : \{w})",
        "(lim : Num)",
        "(m0 : \{w})",
        "(xs0 : \{lw})",
        "(hd0 : \{ht})",
        "(fp : \{rty})",
        "T",
        if prev {
          "F"
        } else {
          "T"
        },
        if merge {
          if last {
            left
          } else {
            "(top : \{w})"
          }
        } else {
          "(top : \{w})"
        },
        if merge {
          "(qs : \{lw})"
        } else {
          prefix
        },
        if merge {
          left
        } else {
          "(m : \{w})"
        },
        if merge {
          other_suffix
        } else {
          suffix
        },
        if merge {
          nh
        } else {
          "(hd : \{ht})"
        },
        if merge {
          "tlsf_pop_fl(\{hp},(fl : \{w}),(sb : (Num) -> \{w}),\{rem})"
        } else {
          "(fl : \{w})"
        },
        if merge {
          "tlsf_pop_sb(\{hp},(sb : (Num) -> \{w}),\{rem})"
        } else {
          "(sb : (Num) -> \{w})"
        },
        if merge {
          "tlsf_pop_bl(\{hp},(bl : \{bt}),\{rem})"
        } else {
          "(bl : \{bt})"
        },
        if merge {
          "V_num(ConstInt32((p : \{w})))"
        } else if prev {
          "V_num(ConstInt32(word_add((m : \{w}),word(4))))"
        } else {
          "(l1 : Value)"
        },
        if merge {
          "V_num(ConstInt32((hd : \{ht})(\{left})))"
        } else {
          "(l2 : Value)"
        },
      ])
      let fold_tac = free_at(
        "path fold",
        seq([
          rw([@class.eta_ax()]),
          @tactics.match_mp_tac(
            @simp.rewrite_rule(ths(norm + [@class.eta_ax()]))(fold),
          ),
          arw(
            norm +
            [
              thm("tlsf_free_left"),
              thm("tlsf_free_right"),
              thm("tlsf_free_end_append"),
              thm("tlsf_end"),
              @lists.hd(),
            ],
          ),
        ]),
      )
      let callback : @tactics.Tactic = if merge {
        g => {
          let (_, _, _, labels) = triple_l_terms(g.1)
          let body = @simp.rewrite_rule(ths(norm))(
            inst(
              thm(
                "tlsf_free_merge_\{dir}" +
                (if last { "_last_body" } else { "_interior_body" }),
              ),
              [
                "(G : \{gt})",
                "(fs : List[Cl])",
                "(tabs : List[(Tab_t,List[V_ref])])",
                "(inst : Inst)",
                "(rp : \{sassn})",
                show(labels),
                "(qs : \{lw})",
                "(n : \{w})",
                "(ts : \{lw})",
                left,
                right,
                "(d : \{w})",
                "(pop : Num)",
                "(push : Num)",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(fl : \{w})",
                "(sb : (Num) -> \{w})",
                "(bl : \{bt})",
                "(us : \{lw})",
                "(vs : \{lw})",
                if prev {
                  "V_num(ConstInt32(word_add((m : \{w}),word(4))))"
                } else {
                  "(l1 : Value)"
                },
                "(l2 : Value)",
                "(fp : \{rty})",
              ],
            ),
          )
          free_g_conseq(body, same, fold_tac)(g)
        }
      } else {
        g => {
          let (p, _, _, labels) = triple_l_terms(g.1)
          let nilth = inst(thm("sl_nil_g"), [
            "(G : \{gt})",
            "(fs : List[Cl])",
            "(tabs : List[(Tab_t,List[V_ref])])",
            "(inst : Inst)",
            "(rp : \{sassn})",
            show(p),
            show(labels),
          ])
          free_g_conseq(nilth, same, fold_tac)(g)
        }
      }
      let facts = if missing && prev {
        @tactics.all_tac
      } else if prev {
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_free_member"), [
              "(d : \{w})",
              "(lim : Num)",
              "(top : \{w})",
              xs,
              "(hd : \{ht})",
              "(m : \{w})",
              "(p : \{w})",
            ]),
          ),
          arw(norm + [@lists.mem_append(), @lists.mem()]),
          strip,
          @tactics.rule_assum_tac(
            @simp.rewrite_rule(ths([thm("tlsf_block_ok")])),
          ),
          split_conjs(),
        ])
      } else {
        seq([
          @tactics.mp_tac(
            if missing {
              inst(thm("tlsf_free_last"), [
                prefix,
                "(d : \{w})",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(m : \{w})",
              ])
            } else {
              inst(thm("tlsf_free_next_geometry"), [
                prefix,
                if merge {
                  other_suffix
                } else {
                  "(zs : \{lw})"
                },
                "(d : \{w})",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(m : \{w})",
                "(p : \{w})",
              ])
            },
          ),
          arw(norm),
          if missing {
            @tactics.disch_then(th => @tactics.assume_tac(@bool.conjunct2(th)))
          } else {
            seq([
              strip,
              @tactics.undisch_tac(
                tm(
                  "(p : \{w}) == word_add(word_add((m : \{w}),tlsf_size((hd : \{ht})(m))),word(8))",
                ),
              ),
              @tactics.disch_then(th => @tactics.assume_tac(@equal.sym(th))),
            ])
          },
        ])
      }
      let merge_facts = if merge {
        seq([
          @tactics.mp_tac(
            @simp.rewrite_rule(ths(norm))(
              inst(thm("tlsf_free_pair_geometry"), [
                "(qs : \{lw})",
                other_suffix,
                left,
                right,
                "(d : \{w})",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(m : \{w})",
              ]),
            ),
          ),
          arw(norm),
          strip,
          @tactics.rule_assum_tac(
            @simp.rewrite_rule(ths([thm("tlsf_block_ok")])),
          ),
          split_conjs(),
          @tactics.mp_tac(
            @simp.rewrite_rule(ths(norm))(
              inst(thm("tlsf_free_bin_decompose"), [
                xs,
                "(hd : \{ht})",
                "(bl : \{bt})",
                "(m : \{w})",
                "(p : \{w})",
              ]),
            ),
          ),
          arw(norm + [@lists.mem_append(), @lists.mem()]),
          strip,
          @tactics.mp_tac(
            @simp.rewrite_rule(ths(norm))(
              inst(thm("tlsf_free_merge_\{dir}_work"), [
                "(xs0 : \{lw})",
                "(hd0 : \{ht})",
                "(m0 : \{w})",
                "(qs : \{lw})",
                other_suffix,
                left,
                right,
                "(d : \{w})",
                "(lim : Num)",
                "(top : \{w})",
                "(hd : \{ht})",
                "(bl : \{bt})",
                "(us : \{lw})",
                "(vs : \{lw})",
              ]),
            ),
          ),
          arw(norm),
          strip,
        ])
      } else {
        @tactics.all_tac
      }
      let _ = lemma(
        "tlsf_free_\{dir}_" +
        (if missing {
          "boundary_path"
        } else if !merge {
          "used_path"
        } else if last {
          "last_path"
        } else {
          "interior_path"
        }),
        "\{vars}, \{cond} → sl_triple_g(G,fs,tabs,inst,rp,\{show(tt[0])},tlsf_free_\{dir}(d,pop,push),\{target},labels)",
        () => {
          seq([
            gen,
            strip,
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths(norm))),
            facts,
            merge_facts,
            rw([thm("tlsf_free_\{dir}_parts")]),
            @tactics.match_mp_tac(thm("sl_seq_g")),
            @tactics.exists_tac(tt[2]),
            both(
              free_at("test lift", free_lift(tst)),
              free_at(
                "branch",
                seq([
                  @tactics.match_mp_tac(
                    inst(
                      thm(
                        if merge {
                          "tlsf_free_if_taken"
                        } else {
                          "tlsf_free_if_skipped"
                        },
                      ),
                      [
                        "(G : \{gt})",
                        "(fs : List[Cl])",
                        "(tabs : List[(Tab_t,List[V_ref])])",
                        "(inst : Inst)",
                        "(rp : \{sassn})",
                        show(st1[1]),
                        show(st1[2]),
                        if missing {
                          "(word(0) : \{w})"
                        } else {
                          "(wasm_bool(!tlsf_used(\{hp})) : \{w})"
                        },
                        "tlsf_free_\{dir}_body((d : \{w}),(pop : Num),(push : Num))",
                        target,
                        "(labels : List[\{sassn}])",
                      ],
                    ),
                  ),
                  both(
                    arw([thm("wasm_bool_zero")]),
                    seq([
                      gen,
                      @tactics.pop_assum_list(all => {
                        seq(
                          all
                          .to_array()
                          .filter(th => {
                            let c = @kernel.concl(th)
                            !(@basics.is_eq(c) &&
                            head_name(@equal.rhs(c)) == "word_add")
                          })
                          .map(@tactics.assume_tac),
                        )
                      }),
                      free_at("callback", callback),
                    ]),
                  ),
                ]),
              ),
            ),
          ])
        },
      )
    }
  }
}
