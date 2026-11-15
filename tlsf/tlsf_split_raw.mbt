///|
fn prove_tlsf_split_raw() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let rty0 = "(gs : List[Value]) => (ms : Num) => star(\{cell("m", "hd")}, (fp : \{rty})(gs, ms))"
  let out = "word_or(word_and((hd : \{w}), word(4294967294)), word(1))"
  let rty1 = "(gs : List[Value]) => (ms : Num) => star(\{cell("m", out)}, (fp : \{rty})(gs, ms))"
  let ls = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let ls1 = "[\{i("m")}, (l1 : Value), \{i("word_and((hd : \{w}), word(4294967292))")}, \{i("n")}, (l4 : Value), (l5 : Value)]"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let after = "st((NIL : List[Value]), \{ls1}, \{rty0})"
  let vars = "∀ G : (Num, (List[Value], List[Value], Num, \{heap}) -> Bool, (List[Value], List[Value], Num, \{heap}) -> Bool) -> Bool, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ m : \{w}, ∀ n : \{w}, ∀ hd : \{w}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let stmt = "\{vars}, !word_ugt(word_and(hd, word(4294967292)), word_add(n, word(264))) → sl_triple_g(G, fs, tabs, inst, \{falsep}, st(NIL, \{ls}, \{rty0}), tlsf_split_code(d, push), (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == \{i("m")} && EL(3, lc) == \{i("n")} && vs == NIL && (\{rty1})(gs, ms, h), NIL)"
  let _ = sym_prove(
    "tlsf_split_no_remainder",
    stmt,
    [],
    [],
    afters=[after, falsep, falsep],
    rws=[
      thm("tlsf_size"),
      @lists.el(),
      @lists.hd(),
      @lists.tl(),
      @lists.length(),
    ],
  )
}
