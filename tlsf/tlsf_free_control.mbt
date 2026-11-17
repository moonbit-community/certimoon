///|
fn prove_tlsf_free_control() -> Unit raise {
  let w = w32
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}"
  let vars = "\{env}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ c : \{w}, ∀ body : List[B_e], ∀ Q : \{sassn}, ∀ labels : List[\{sassn}]"
  for taken in [true, false] {
    let bs = if taken { "(body : List[B_e])" } else { "(NIL : List[B_e])" }
    let cb = "∀ ls2 : List[\{sassn}], sl_triple_g((G : \{gt}),(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),(rp : \{sassn}),st(NIL,(lc : List[Value]),(R : \{rty})),\{bs},(Q : \{sassn}),ls2)"
    let cond = if taken {
      "!((c : \{w}) == word(0))"
    } else {
      "(c : \{w}) == word(0)"
    }
    let rule = @simp.rewrite_rule(ths([@lists.append()]))(
      inst(thm("sl_if_st_g"), [
        "(G : \{gt})",
        "(fs : List[Cl])",
        "(tabs : List[(Tab_t,List[V_ref])])",
        "(inst : Inst)",
        "(rp : \{sassn})",
        "(NIL : List[Value])",
        "(lc : List[Value])",
        "(R : \{rty})",
        "(c : \{w})",
        "Tbv(NONE)",
        "(body : List[B_e])",
        "(NIL : List[B_e])",
        "(Q : \{sassn})",
        "(labels : List[\{sassn}])",
      ]),
    )
    let _ = lemma(
      if taken {
        "tlsf_free_if_taken"
      } else {
        "tlsf_free_if_skipped"
      },
      "\{vars}, \{cond} && (\{cb}) → sl_triple_g(G,fs,tabs,inst,rp,st([\{i("c")}],lc,R),[If(Tbv(NONE),body,NIL)],Q,labels)",
      () => {
        seq([
          gen,
          strip,
          @tactics.match_mp_tac(rule),
          arw([]),
          @tactics.match_mp_tac(thm("sl_block_st_g")),
          beta_goal(),
          rw([@lists.append(), @class.eta_ax()]),
          @tactics.first_x_assum(th => @tactics.match_accept_tac(th)),
        ])
      },
    )
  }
}
