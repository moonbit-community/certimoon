///|
fn prove_tlsf_ensure_amounts() -> Unit raise {
  let w = w32
  let failvc = seq([
    @tactics.exists_tac(tm("(NIL : List[Value])")),
    @tactics.exists_tac(tm("[V_num(ConstInt32((word(0) : \{w})))]")),
    @simp.asm_rewrite_tac(ths([@lists.append()])),
    @tactics.first_x_assum(th => {
      @tactics.match_mp_tac(
        inst(th, ["(gs : List[Value])", "(ms : Num)", "(h : \{heap})"]),
      )
    }),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let e = "(e : \{w})"
  let m = "(m : \{w})"
  let lc = "[\{i(m)},\{i(e)}]"
  let roargs = "(d : \{w}),(m : \{w}),(hdr : \{w}),(lim : Num),(before : \{heap}),(fp : \{rty})"
  let ro = "tlsf_ensure_ro(\{roargs})"
  let used = "word_jushr(word_add(\{e},word(65543)),word(16))"
  let free = "word_jushr(word_add(word_sub(\{e},tlsf_size((hdr : \{w}))),word(65535)),word(16))"
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ e : \{w}, ∀ R : \{rty}"
  ignore(
    sym_prove(
      "tlsf_ensure_used_amount_raw",
      "\{vars}, sl_triple(st(NIL,\{lc},R),tlsf_ensure_used_amount(d,pop,push),st([\{i(used)}],\{lc},R))",
      [],
      () => [],
    ),
  )
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ e : \{w}, ∀ hdr : \{w}, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  ignore(
    sym_prove(
      "tlsf_ensure_free_amount_raw",
      "\{vars}, sl_triple(st(NIL,\{lc},\{ro}),tlsf_ensure_free_amount(d,pop,push),st([\{i(free)}],\{lc},\{ro}))",
      [],
      () => [],
      rules=step_rules + ["st_ensure_load_header"],
      rws=[thm("tlsf_size")],
    ),
  )
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}"
  let vars = "\{env}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lc0 : List[Value], ∀ R : \{rty}, ∀ ls : List[\{sassn}]"
  let tr = (p : String, q : String) => {
    "sl_triple_g(G,fs,tabs,inst,rp,\{p},tlsf_ensure_guard(d,pop,push),\{q},ls)"
  }
  let sf = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let state = (stack : String) => {
    "st(\{stack},(lc0 : List[Value]),(R : \{rty}))"
  }
  ignore(
    sym_prove(
      "tlsf_ensure_guard_failure",
      "\{vars}, (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs,ms,h) → rp([\{i("word(0)")}],lc0,gs,ms,h)) → \{tr(state("["+i("word(4294967295)")+"]"),sf)}",
      [],
      () => [failvc],
    ),
  )

  ignore(
    sym_prove(
      "tlsf_ensure_guard_success",
      "\{vars}, ∀ c : \{w}, !(c == word(4294967295)) → \{tr(state("["+i("c")+"]"),state("NIL"))}",
      [],
      () => [],
    ),
  )
}
