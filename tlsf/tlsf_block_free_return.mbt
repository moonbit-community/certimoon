///|
fn define_tlsf_block_free_return() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let a = page_arguments(model + [("m", w), ("fp", rty)])
  let newmodel = model.map(v => {
    if ["top", "xs", "hd", "fl", "sb", "bl"].contains(v.0) {
      (v.0 + "2", v.1)
    } else {
      v
    }
  })
  let newargs = page_arguments(newmodel)
  let worlds = newmodel.filter(v => {
    ["top2", "xs2", "hd2", "fl2", "sb2", "bl2"].contains(v.0)
  })
  let exworlds = worlds.map(v => "∃ " + v.0 + " : " + v.1 + ", ").join("")
  let q = "tlsf_small_return_post(" + a + ")"
  def(
    "tlsf_small_return_post",
    "\{q} == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [V_num(ConstInt32((word(0) : \{w})))] && ms == (lim : Num) && (\{exworlds}star(tlsf_allocator(\{newargs}),(fp : \{rty})(gs,ms),h)))",
  )
}

// Close the page-reclamation call against the existing compiled TLSF free,
// pop, and push closures, transporting the remaining small-page invariant.

///|
fn prove_tlsf_block_free_return() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let model = page_model_variables()
  let vs = model + [("m", w), ("fp", rty)]
  let v = page_quantify(vs)
  let a = page_arguments(vs)
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _args = page_arguments(model)
  let sargs = page_arguments(
    model.filter(v => {
      ["d", "hd", "ps", "sz", "loc", "cached", "live", "fast", "partial"].contains(
        v.0,
      )
    }),
  )
  let small = "tlsf_small(" + sargs + ")"
  let frame = "(gs : List[Value]) => (ms : Num) => star(\{small},(fp : \{rty})(gs,ms))"
  let fargs = "(d : \{w}),(m : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(\{frame})"
  let fpost = "tlsf_free_post(" + fargs + ")"
  let backingargs = ["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"]
    .map(n => model.filter(v => v.0 == n)[0])
    .map(v => "(" + v.0 + " : " + v.1 + ")")
    .join(",")
  let backing = "tlsf_small_backing(" + backingargs + ")"
  let newmodel = model.map(v => {
    if ["top", "xs", "hd", "fl", "sb", "bl"].contains(v.0) {
      (v.0 + "2", v.1)
    } else {
      v
    }
  })
  let _newargs = page_arguments(newmodel)
  let worlds = newmodel.filter(v => {
    ["top2", "xs2", "hd2", "fl2", "sb2", "bl2"].contains(v.0)
  })
  let _exworlds = worlds.map(v => "∃ " + v.0 + " : " + v.1 + ", ").join("")
  let q = "tlsf_small_return_post(" + a + ")"
  let transport = ["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"].map(n => {
      "(" + n + " : " + model.filter(v => v.0 == n)[0].1 + ")"
    }) +
    ["(m : " + w + ")", "(xs2 : " + lw + ")", "(hd2 : " + ht + ")"]
  let fold = lemma(
    "tlsf_small_return_post_fold",
    "\{v} ∀ res : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{backing} && !MEM(m,ps) && \{fpost}(res,gs,ms,h) → \{q}(res,gs,ms,h)",
    seq([
      gen,
      rw([thm("tlsf_free_post"), thm("tlsf_small_return_post")]),
      strip,
      arw([]),
      g => {
        @tactics.assume_tac(
          block_under(inst(thm("tlsf_small_free_backing"), transport), g),
        )(g)
      },
      g => {
        @tactics.assume_tac(
          block_under(
            inst(
              thm("tlsf_small_free_heap"),
              transport +
              [
                "(d : " + w + ")",
                "(fast : (Num) -> " + lw + ")",
                "(partial : (Num) -> " + lw + ")",
              ],
            ),
            g,
          ),
        )(g)
      },
      seq(
        worlds.map(v => @tactics.exists_tac(tm("(" + v.0 + " : " + v.1 + ")"))),
      ),
      rw([thm("tlsf_allocator_frame")]),
      arw([]),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw([]),
    ]),
  )
  let env = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num"
  let path = inst(thm("tlsf_free_all"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : " + w + ")",
    "(pop : Num)",
    "(push : Num)",
    "(free_idx : Num)",
    "(m : " + w + ")",
    "(lim : Num)",
    "(top : " + w + ")",
    "(xs : " + lw + ")",
    "(hd : " + ht + ")",
    "(fl : " + w + ")",
    "(sb : (Num) -> " + w + ")",
    "(bl : " + bt + ")",
    frame,
    "(vs0 : List[Value])",
    "(lc0 : List[Value])",
  ])
  let natives = show(@basics.dest_imp(@kernel.concl(path)).0)
  let pre = call_pre(
    "tlsf_free_pre(" + fargs + ")",
    "(vs0 : List[Value])",
    "(lc0 : List[Value])",
  )
  let post = call_post(q, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let _ = lemma(
    "tlsf_small_return_all",
    "\{env}, \{v} ∀ vs0 : List[Value], ∀ lc0 : List[Value], \{backing} && !MEM(m,ps) && \{natives} → sl_triple_m(fs,tabs,inst,\{pre},[Call(free_idx)],\{post},NIL)",
    seq([
      gen,
      strip,
      initialize_m_conseq(
        path,
        same_tac(),
        seq([
          gen,
          beta_goal(),
          strip,
          subst_vars(),
          @tactics.mp_tac(
            inst(
              fold,
              vs.map(v => "(" + v.0 + " : " + v.1 + ")") +
              [
                "(res : List[Value])",
                "(gs : List[Value])",
                "(ms : Num)",
                "(h : " + heap + ")",
              ],
            ),
          ),
          arw([]),
          @tactics.disch_tac,
          @tactics.exists_tac(tm("(res : List[Value])")),
          arw([]),
        ]),
      ),
    ]),
  )
}
