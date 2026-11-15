// During free the active block is free but absent from the bins. Marking
// it used in the pure model permits the temporary adjacent-free states.

///|
fn define_tlsf_free_state() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  def(
    "tlsf_release",
    "tlsf_release((hd : \{ht}),(m : \{w})) == tlsf_put(hd,m,word_and(hd(m),word(4294967294)))",
  )
  def(
    "tlsf_merge_size",
    "tlsf_merge_size((a : \{w}),(b : \{w})) == word_add(word_add(tlsf_size(a),tlsf_size(b)),word(8))",
  )
  def(
    "tlsf_merge_header",
    "tlsf_merge_header((a : \{w}),(b : \{w})) == word_or(tlsf_merge_size(a,b),word_and(b,word(2)))",
  )
  def(
    "tlsf_merge_headers",
    "tlsf_merge_headers((hd : \{ht}),(m : \{w}),(r : \{w})) == tlsf_put(hd,m,tlsf_merge_header(hd(m),hd(r)))",
  )
  def(
    "tlsf_free_geom",
    "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(m : \{w})) == tlsf_physical_ok(d,lim,top,xs,tlsf_mark(hd,m))",
  )
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let ps = [
    cell("tlsf_top_cell((d : " + w + "))", "top"),
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),(hd : \{ht}))",
    cell("m", "(hd : " + ht + ")((m : " + w + "))"),
    cell(
      "word_add((m : " + w + "),word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd : \{ht})(m))))",
    "tlsf_regions((m : \{w}),(zs : \{lw}),(hd : \{ht}))",
    "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
  ]
  let mut owned = ps[ps.length() - 1]
  for k = ps.length() - 2; k >= 0; k = k - 1 {
    owned = "star(\{ps[k]},\{owned})"
  }
  def(
    "tlsf_free_pending",
    "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),(m : \{w}),(zs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt})) == ((h : \{heap}) => tlsf_free_geom(d,lim,top,\{xs},hd,m) && !tlsf_used(hd(m)) && tlsf_bins_match(\{xs},tlsf_mark(hd,m),bl) && \{owned}(h))",
  )
  let params = "(d : \{w}),(m : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(fp : \{rty})"
  let client = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  let large = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let bytes = "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd : \{ht})(m))))"
  def(
    "tlsf_free_pre",
    "tlsf_free_pre(\{params}) == ((args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [V_num(ConstInt32(m))] && ms == lim && MEM(m,xs) && tlsf_used(hd(m)) && star(\{large},star(\{bytes},\{client}),h))",
  )
  def(
    "tlsf_free_post",
    "tlsf_free_post(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [V_num(ConstInt32((word(0) : \{w})))] && ms == lim && (∃ top2 : \{w}, ∃ xs2 : \{lw}, ∃ hd2 : \{ht}, ∃ fl2 : \{w}, ∃ sb2 : (Num) -> \{w}, ∃ bl2 : \{bt}, ∃ r : \{w}, MEM(r,xs2) && !tlsf_used(hd2(r)) && val(r) <= val(m) && val(m)+8+val(tlsf_size(hd(m))) <= val(r)+8+val(tlsf_size(hd2(r))) && (∀ x : \{w}, MEM(x,xs) && !(x == m) && tlsf_used(hd(x)) → MEM(x,xs2) && hd2(x) == hd(x)) && star(tlsf_large(d,lim,top2,xs2,hd2,fl2,sb2,bl2),\{client},h)))",
  )
}
