// Both paths after the closed Memory::take call. Failure returns immediately;
// success initializes only its newly acquired payload.

///|
fn define_tlsf_page_allocate_tail() -> Unit raise {
  let defs = [
    thm("tlsf_page_allocate_guard"),
    thm("tlsf_page_allocate_fill"),
    @lists.append(),
  ]
  let code = @equal.rhs(
    @kernel.concl(
      @simp.rewrite_conv(ths(defs))(
        tm(
          "APPEND(tlsf_page_allocate_guard((take_idx : Num)),tlsf_page_allocate_fill(take_idx))",
        ),
      ),
    ),
  )
  ignore(
    program("tlsf_page_allocate_tail", show(code), params=["(take_idx : Num)"]),
  )
  let _ = lemma(
    "tlsf_page_allocate_call_tail",
    "∀ take_idx : Num, tlsf_page_allocate_code(take_idx) == APPEND(tlsf_page_allocate_call(take_idx),tlsf_page_allocate_tail(take_idx))",
    () => {
      @simp.rewrite_tac(
        ths([
          thm("tlsf_page_allocate_code"),
          thm("tlsf_page_allocate_call"),
          thm("tlsf_page_allocate_tail"),
          @lists.append(),
        ]),
      )
    },
  )
}

///|
fn prove_tlsf_page_allocate_tail() -> Unit raise {
  let w = w32
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let own = "(gs : List[Value]) => (ms : Num) => \{small_star(["tlsf_bytes(val("+p+")+8,(cap : Num))","(fp : "+rty+")(gs,ms)"])}"
  let oldlc = "[\{i(s)},(l1 : Value),(l2 : Value),(l3 : Value),(l4 : Value),(l5 : Value)]"
  let newlc = "[\{i(s)},\{i(p)},(l2 : Value),(l3 : Value),(l4 : Value),(l5 : Value)]"
  let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{i(p)}] && star(tlsf_page_allocate_fresh(\{p},(cap : Num),val(\{s})),(fp : \{rty})(gs,ms),h)"
  let env = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ take_idx : Num"
  let locals = "∀ s : \{w}, ∀ l1 : Value, ∀ l2 : Value, ∀ l3 : Value, ∀ l4 : Value, ∀ l5 : Value"
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    beta_goal(),
    @tactics.try_tac(@tactics.disch_tac),
    @simp.asm_rewrite_tac(ths([])),
  ])
  ignore(
    sym_prove(
      "tlsf_page_allocate_tail_success",
      "\{env}, ∀ p : \{w}, ∀ cap : Num, \{locals}, ∀ fp : \{rty}, tlsf_page_allocate_geometry(p,cap,val(s)) && !(p == word(0)) → sl_triple_g(G,fs,tabs,inst,rp,st([\{i(p)}],\{oldlc},\{own}),tlsf_page_allocate_tail(take_idx),\{q},[rp])",
      [
        "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => F",
      ],
      () => [same],
      afters=[
        "st(NIL," + newlc + "," + own + ")",
        @logic.sa_false,
        @logic.sa_false,
        @logic.sa_false,
      ],
      chunks=[thm("tlsf_page_allocate_fill_all")],
      kind="lemma",
    ),
  )
  let z = i("word(0)")
  let failurepost = @logic.sa_false
  let zerolc = "[" +
    i(s) +
    "," +
    z +
    ",(l2 : Value),(l3 : Value),(l4 : Value),(l5 : Value)]"
  let callback = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (R : \{rty})(gs,ms,h) → (rp : \{sassn})([\{z}],\{zerolc},gs,ms,h)"
  ignore(
    sym_prove(
      "tlsf_page_allocate_tail_failure",
      "\{env}, \{locals}, ∀ R : \{rty}, (\{callback}) → sl_triple_g(G,fs,tabs,inst,rp,st([\{z}],\{oldlc},R),tlsf_page_allocate_tail(take_idx),\{failurepost},[rp])",
      [
        "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => F",
      ],
      () => {
        [
          seq([
            same,
            @tactics.exists_tac(tm("(NIL : List[Value])")),
            @tactics.exists_tac(tm("[" + z + "]")),
            @simp.rewrite_tac(ths([@lists.append()])),
            small_meson(ths([])),
          ]),
        ]
      },
      afters=[
        @logic.sa_false, @logic.sa_false, @logic.sa_false, @logic.sa_false,
      ],
      chunks=[thm("tlsf_page_allocate_fill_all")],
      kind="lemma",
    ),
  )
}
