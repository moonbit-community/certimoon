// A small regression for composing a verified multi-instruction fragment.
// The client assertion and locals are arbitrary, so framing is exercised too.

///|
fn prove_chunk_example() -> Unit raise {
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.conv_tac(@words.word_reduce_conv),
  ])
  let one = "V_num(ConstInt32((word(1) : \{w32})))"
  let two = "V_num(ConstInt32((word(2) : \{w32})))"
  let three = "V_num(ConstInt32((word(3) : \{w32})))"
  let code = "[EConstNum(ConstInt32((word(1) : \{w32}))),EConstNum(ConstInt32((word(2) : \{w32})))]"
  let vars = "∀ lc : List[Value], ∀ R : \{rty}"
  let chunk = sym_prove(
    "chunk_pair",
    "\{vars}, sl_triple(st(NIL,lc,R),\{code},st([\{one},\{two}],lc,R))",
    [],
    [same],
    kind="lemma",
  )
  ignore(
    sym_prove(
      "example_chunks",
      "\{vars}, sl_triple(st(NIL,lc,R),[EConstNum(ConstInt32((word(1) : \{w32}))),EConstNum(ConstInt32((word(2) : \{w32}))),Binop(T_i32,Binop_i(Add))],st([\{three}],lc,R))",
      [],
      [same],
      chunks=[chunk],
    ),
  )
}

///|
fn prove_chunk_control_example() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((word(\{x}) : \{w})))"
  let one = i("1")
  let two = i("2")
  let code = "[EConstNum(ConstInt32((word(1) : \{w}))),EConstNum(ConstInt32((word(2) : \{w})))]"
  let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{one},\{two}] && (R : \{rty})(gs,ms,h)"
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.try_tac(@tactics.disch_tac),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let chunk = sym_prove(
    "chunk_hidden_locals",
    "∀ lc : List[Value], ∀ R : \{rty}, sl_triple(st(NIL,lc,R),\{code},\{q})",
    [],
    [same],
    kind="lemma",
  )
  ignore(
    sym_prove(
      "example_chunks_hidden_locals",
      "∀ lc : List[Value], ∀ R : \{rty}, sl_triple(st(NIL,lc,R),\{code},\{q})",
      [],
      [],
      chunks=[chunk],
    ),
  )
  let gt = "(Num,(List[Value],List[Value],Num,\{heap}) -> Bool,(List[Value],List[Value],Num,\{heap}) -> Bool) -> Bool"
  let rp = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{one}] && (R : \{rty})(gs,ms,h)"
  let ret = seq([
    same,
    @tactics.exists_tac(tm("(NIL : List[Value])")),
    @simp.asm_rewrite_tac(ths([@lists.append()])),
  ])
  let dead_path = seq([
    same,
    @tactics.undisch_tac(tm("(word(1) : " + w + ") == word(0)")),
    @tactics.conv_tac(@words.word_reduce_conv),
  ])
  ignore(
    sym_prove(
      "example_chunks_return",
      "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ lc : List[Value], ∀ R : \{rty}, sl_triple_g(G,fs,tabs,inst,\{rp},st(NIL,lc,R),[EConstNum(ConstInt32((word(1) : \{w}))),If(Tbv(NONE),[EConstNum(ConstInt32((word(1) : \{w}))),Return],NIL),EConstNum(ConstInt32((word(2) : \{w})))],\{sa_false},[\{rp}])",
      [],
      [ret, dead_path],
      afters=[sa_false],
    ),
  )
}

///|
fn prove_g_chunk_example() -> Unit raise {
  let w = w32
  let gt = "(Num,(List[Value],List[Value],Num," +
    heap +
    ") -> Bool,(List[Value],List[Value],Num," +
    heap +
    ") -> Bool) -> Bool"
  let i = "V_num(ConstInt32((word(1) : " + w + ")))"
  let vars = "∀ G : " +
    gt +
    ", ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ lc : List[Value], ∀ R : " +
    rty +
    ", "
  let rp = "(vs : List[Value]) => (lc2 : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => vs == [" +
    i +
    "] && (R : " +
    rty +
    ")(gs,ms,h)"
  let code = "[EConstNum(ConstInt32((word(1) : " + w + "))),Return]"
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.exists_tac(tm("(NIL : List[Value])")),
    @simp.asm_rewrite_tac(ths([@lists.append()])),
  ])
  let chunk = sym_prove(
    "chunk_general_return",
    vars +
    "sl_triple_g(G,fs,tabs,inst," +
    rp +
    ",st(NIL,lc,R)," +
    code +
    "," +
    sa_false +
    ",[" +
    rp +
    "])",
    [],
    [same],
    kind="lemma",
  )
  ignore(
    sym_prove(
      "example_general_chunks_return",
      vars +
      "sl_triple_g(G,fs,tabs,inst," +
      rp +
      ",st(NIL,lc,R),[EConstNum(ConstInt32((word(1) : " +
      w +
      "))),Return,Unreachable]," +
      sa_false +
      ",[" +
      rp +
      "])",
      [],
      [],
      chunks=[chunk],
    ),
  )
}
