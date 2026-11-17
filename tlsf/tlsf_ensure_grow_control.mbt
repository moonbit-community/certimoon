///|
fn prove_tlsf_ensure_grow_control() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let args = [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(rp : \{sassn})",
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(lc0 : List[Value])",
  ]
  let old = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && (R : \{rty})(gs,lim,h)"
  let fresh = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num)+val((c : \{w}))*65536 && star((R : \{rty})(gs,lim),pts(lim,REPLICATE(val(c)*65536,(word(0) : Word[8]))),h)"
  let state = (stack : String, r : String) => {
    "st(\{stack},(lc0 : List[Value]),\{r})"
  }
  let p = state(
    "[" + i("c") + "]",
    "(gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => ms == (lim : Num) && (R : " +
    rty +
    ")(gs,ms,h)",
  )
  let good = state("NIL", fresh)
  let neg = state("[" + i("word(4294967295)") + "]", old)
  let pos = state("[" + i("word(DIV((lim : Num),65536))") + "]", fresh)
  let cap = "DIV((lim : Num),65536)+val((c : \{w})) <= 65536"
  let raw = @simp.rewrite_rule(ths([@lists.append()]))(
    inst(thm("st_memory_grow"), [
      "(NIL : List[Value])",
      "(lc0 : List[Value])",
      "(lim : Num)",
      "(R : \{rty})",
      "(c : \{w})",
    ]),
  )
  let rt = args_of(@kernel.concl(raw), "sl_triple", 3).unwrap()
  let tr = (p : String, code : String) => {
    "sl_triple_g(G,fs,tabs,inst,rp,\{p},\{code},(Q : \{sassn}),(labels : List[\{sassn}]))"
  }
  let fail = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (\{old})(gs,ms,h) → (rp : \{sassn})([\{i("word(0)")}],(lc0 : List[Value]),gs,ms,h)"
  let success = "\{cap} → \{tr(good,"(rest : List[B_e])")}"
  let guard_code = "tlsf_ensure_guard((d : \{w}),(pop : Num),(push : Num))"
  let tail = "APPEND(\{guard_code},(rest : List[B_e]))"
  let all = "APPEND([Memory_grow],\{tail})"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lc0 : List[Value], ∀ lim : Num, ∀ c : \{w}, ∀ R : \{rty}, ∀ rest : List[B_e], ∀ Q : \{sassn}, ∀ labels : List[\{sassn}]"
  let sf = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let failure = inst(
    thm("tlsf_ensure_guard_failure"),
    args + [old, "(labels : List[" + sassn + "])"],
  )
  let ok = inst(
    thm("tlsf_ensure_guard_success"),
    args +
    [
      fresh,
      "(labels : List[" + sassn + "])",
      "(word(DIV((lim : Num),65536)) : \{w})",
    ],
  )
  let cap_pos = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{cap} && (\{pos})(vs,lc,gs,ms,h)"
  let or_th = @simp.rewrite_rule(ths([@class.eta_ax()]))(
    inst(
      thm("sl_or_g"),
      args[0:5].to_owned() +
      [neg, cap_pos, "(Q : \{sassn})", tail, "(labels : List[\{sassn}])"],
    ),
  )
  let _ = lemma(
    "tlsf_ensure_grow_control",
    "\{vars}, (lim : Num) <= 4294967296 && (\{fail}) && (\{success}) → \{tr(p,all)}",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(thm("sl_seq_g")),
        @tactics.exists_tac(rt[2]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.match_mp_tac(thm("sl_triple_g_of")),
              @tactics.conj_tac,
              @tactics.first(
                @list.List([
                  solve(call_free_tac()),
                  solve(
                    seq([
                      @tactics.match_mp_tac(thm("sl_triple_l_of")),
                      @tactics.accept_tac(raw),
                    ]),
                  ),
                ]),
              ),
            ]),
            seq([
              @tactics.match_mp_tac(or_th),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.match_mp_tac(thm("sl_seq_g")),
                    @tactics.exists_tac(tm(sf)),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([@tactics.match_mp_tac(failure), arw([])]),
                        @tactics.match_accept_tac(thm("sl_false_g")),
                      ]),
                    ),
                  ]),
                  seq([
                    @tactics.match_mp_tac(thm("sl_pure_g")),
                    @tactics.disch_tac,
                    @tactics.match_mp_tac(thm("sl_seq_g")),
                    @tactics.exists_tac(tm(good)),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([
                          rw([@class.eta_ax()]),
                          @tactics.match_mp_tac(ok),
                          @tactics.match_mp_tac(
                            thm("tlsf_page_result_not_failure"),
                          ),
                          arw([]),
                        ]),
                        seq([
                          @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                          arw([]),
                        ]),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
