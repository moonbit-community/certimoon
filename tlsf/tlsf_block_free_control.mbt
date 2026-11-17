// Classifier reads and result-producing conditionals for the inlined branch.

///|
fn prove_tlsf_block_free_control() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let own = "(gs : List[Value]) => (ms : Num) => star(pts(val(word_add((p : \{w}),word(12))),serialise_i32((total : \{w}))),(fp : \{rty})(gs,ms))"
  let lc = "[\{i("p")},\{i("u")},(l2 : Value)]"
  let vc = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.asm_rewrite_tac(
      ths([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
    ),
  ])
  ignore(
    sym_prove(
      "tlsf_block_free_classify_raw",
      "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ u : \{w}, ∀ total : \{w}, ∀ l2 : Value, ∀ fp : \{rty}, sl_triple(st(NIL,\{lc},\{own}),tlsf_block_free_classify(d,free_idx),st([\{i("wasm_bool((u : "+w+") == (total : "+w+"))")}],\{lc},\{own}))",
      [],
      () => [vc],
      kind="lemma",
    ),
  )
  ignore(
    sym_prove(
      "tlsf_block_free_last_test_raw",
      "∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ u : \{w}, ∀ l2 : Value, ∀ R : \{rty}, sl_triple(st(NIL,\{lc},R),tlsf_block_free_last_test(d,free_idx),st([\{i("wasm_bool((u : "+w+") == word(1))")}],\{lc},R))",
      [],
      () => [],
      kind="lemma",
    ),
  )
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}"
  let vars = "\{env}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ c : \{w}, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ Q : \{sassn}, ∀ labels : List[\{sassn}]"
  for taken in [false, true] {
    let cond = if taken {
      "!((c : " + w + ") == word(0))"
    } else {
      "(c : " + w + ") == word(0)"
    }
    let chosen = if taken { "(bs1 : List[B_e])" } else { "(bs2 : List[B_e])" }
    let cb = "∀ ls2 : List[\{sassn}], sl_triple_g((G : \{gt}),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),(rp : \{sassn}),st(NIL,(lc : List[Value]),(R : \{rty})),\{chosen},(Q : \{sassn}),ls2)"
    let rule = @simp.rewrite_rule(ths([@lists.append()]))(
      inst(thm("sl_if_st_g"), [
        "(G : " + gt + ")",
        "(fs : List[Cl])",
        "(tabs : List[(Tab_t,List[V_ref])])",
        "(inst : Inst)",
        "(rp : " + sassn + ")",
        "(NIL : List[Value])",
        "(lc : List[Value])",
        "(R : " + rty + ")",
        "(c : " + w + ")",
        "Tbv(SOME(T_num(T_i32)))",
        "(bs1 : List[B_e])",
        "(bs2 : List[B_e])",
        "(Q : " + sassn + ")",
        "(labels : List[" + sassn + "]) ",
      ]),
    )
    let _ = lemma(
      "tlsf_block_free_if_" + (if taken { "taken" } else { "skipped" }),
      "\{vars}, \{cond} && (\{cb}) → sl_triple_g(G,fs,tabs,inst,rp,st([\{i("c")}],lc,R),[If(Tbv(SOME(T_num(T_i32))),bs1,bs2)],Q,labels)",
      () => {
        seq([
          @tactics.repeat_tac(@tactics.gen_tac),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.match_mp_tac(rule),
          @simp.asm_rewrite_tac(ths([])),
          @tactics.match_mp_tac(thm("sl_block_st_g")),
          beta_goal(),
          @simp.rewrite_tac(ths([@lists.append(), @class.eta_ax()])),
          @tactics.first_x_assum(th => @tactics.match_accept_tac(th)),
        ])
      },
    )
  }
}
