// Ownership at the two boundaries used to compose Memory::take.
// A detached block is still free in the physical chain; its link words
// have returned from the bin predicate to its whole payload.

///|
fn define_tlsf_take_state() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{v} : \{w})))"
  }
  let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), (zs : \{lw})))"
  let ps = [
    cell("word_add(tlsf_base((d : " + w + ")), word(1908))", "top"),
    "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))",
    cell("m", "(hd : " + ht + ")((m : " + w + "))"),
    cell(
      "word_add((m : " + w + "), word(4))",
      "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
    ),
    "tlsf_bytes(val((m : \{w})) + 8, val(tlsf_size((hd : \{ht})(m))))",
    "tlsf_regions((m : \{w}), (zs : \{lw}), (hd : \{ht}))",
    "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))",
  ]
  let mut owned = ps[ps.length() - 1]
  for k = ps.length() - 2; k >= 0; k = k - 1 {
    owned = "star(\{ps[k]}, \{owned})"
  }
  def(
    "tlsf_detached",
    "tlsf_detached((d : \{w}), (lim : Num), (top : \{w}), (ys : \{lw}), (m : \{w}), (zs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})) == ((h : \{heap}) => tlsf_physical_ok(d, lim, top, \{oldxs}, hd) && !tlsf_used(hd(m)) && tlsf_bins_match(\{oldxs}, tlsf_mark(hd, m), bl) && \{owned}(h))",
  )
  def(
    "tlsf_allocated",
    "tlsf_allocated((d : \{w}), (lim : Num), (m : \{w}), (n : \{w}), (oldxs : \{lw}), (oldhd : \{ht}), (client : \{hprop})) == ((h : \{heap}) => !(m == word(0)) && (∃ top2 : \{w}, ∃ xs2 : \{lw}, ∃ hd2 : \{ht}, ∃ fl2 : \{w}, ∃ sb2 : (Num) -> \{w}, ∃ bl2 : \{bt}, tlsf_retains(oldxs,oldhd,xs2,hd2) && MEM(m, xs2) && tlsf_used(hd2(m)) && val(n) <= val(tlsf_size(hd2(m))) && star(tlsf_large(d, lim, top2, xs2, hd2, fl2, sb2, bl2), star(tlsf_bytes(val(m) + 8, val(tlsf_size(hd2(m)))), client), h)))",
  )
  let large = "tlsf_large((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let frame = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
  let p = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [V_num(ConstInt32((s : \{w})))] && 16 <= val(s) && val(s) <= 4160749568 && ms == (lim : Num) && h == (before : \{heap}) && star(\{large}, \{frame}, h)"
  let query = "tlsf_search((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let q = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && ((res == [V_num(ConstInt32((word(0) : \{w})))] && \{query} == word(0) && h == (before : \{heap}) && star(\{large}, \{frame}, h)) || (∃ m : \{w}, res == [V_num(ConstInt32(m))] && m == \{query} && MEM(m, (xs : \{lw})) && !tlsf_used((hd : \{ht})(m)) && tlsf_allocated(d, lim, m, s, (xs : \{lw}), (hd : \{ht}), \{frame}, h)))"
  let params = "(d : \{w}), (s : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (before : \{heap}), (fp : \{rty})"
  def("tlsf_take_pre", "tlsf_take_pre(\{params}) == (\{p})")
  def("tlsf_take_post", "tlsf_take_post(\{params}) == (\{q})")
  def(
    "tlsf_take_success",
    "tlsf_take_success((d : \{w}), (pop : Num), (push : Num)) == APPEND([Local_get(0), Call(pop)], APPEND(tlsf_split_code(d, push), [Local_get(0), Return]))",
  )
  def(
    "tlsf_take_tail",
    "tlsf_take_tail((d : \{w}), (pop : Num), (push : Num)) == [Local_tee(0), If(Tbv(NONE), tlsf_take_success(d, pop, push), NIL), Local_get(0)]",
  )
  let _ = lemma(
    "tlsf_take_code_parts",
    "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, tlsf_take_code(d, pop, push) == APPEND(tlsf_find_code(d), tlsf_take_tail(d, pop, push))",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @simp.rewrite_tac(
          ths([
            thm("tlsf_take_code"),
            thm("tlsf_find_code"),
            thm("tlsf_take_tail"),
            thm("tlsf_take_success"),
            thm("tlsf_split_code"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
}
