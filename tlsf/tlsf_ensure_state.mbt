// Growth keeps client predicates at the old memory length. Newly appended
// zero bytes become allocator-owned; existing client byte ownership is retained.

///|
fn define_tlsf_ensure_state() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  def(
    "tlsf_capacity_at",
    "tlsf_capacity_at((lim : Num),(m : \{w})) == word_sub(word_sub((word(lim) : \{w}),m),word(8))",
  )
  def(
    "tlsf_top_cell",
    "tlsf_top_cell((d : \{w})) == word_add(tlsf_base(d),word(1908))",
  )
  def(
    "tlsf_ensure_expected",
    "tlsf_ensure_expected((s : \{w})) == tlsf_round(tlsf_align(s))",
  )
  def(
    "tlsf_ensure_pages",
    "tlsf_ensure_pages((s : \{w}),(h : \{w})) == (if tlsf_used(h) { word_jushr(word_add(tlsf_ensure_expected(s),word(65543)),word(16)) } else { word_jushr(word_add(word_sub(tlsf_ensure_expected(s),tlsf_size(h)),word(65535)),word(16)) })",
  )
  def(
    "tlsf_extend_headers",
    "tlsf_extend_headers((hd : \{ht}),(m : \{w}),(lim2 : Num)) == tlsf_put(hd,m,word_or(tlsf_capacity_at(lim2,m),word_and(hd(m),word(3))))",
  )
  def(
    "tlsf_append_headers",
    "tlsf_append_headers((hd : \{ht}),(m : \{w}),(oldlim : Num),(lim2 : Num)) == tlsf_put(tlsf_put(hd,m,word_and(hd(m),word(4294967293))),(word(oldlim) : \{w}),word_or(tlsf_capacity_at(lim2,word(oldlim)),word(2)))",
  )
  def(
    "tlsf_grow_headers",
    "tlsf_grow_headers((hd : \{ht}),(m : \{w}),(oldlim : Num),(lim2 : Num)) == (if tlsf_used(hd(m)) { tlsf_append_headers(hd,m,oldlim,lim2) } else { tlsf_extend_headers(hd,m,lim2) })",
  )
  def(
    "tlsf_grow_top",
    "tlsf_grow_top((hd : \{ht}),(m : \{w}),(oldlim : Num)) == (if tlsf_used(hd(m)) { (word(oldlim) : \{w}) } else { m })",
  )
  def(
    "tlsf_grow_chain",
    "tlsf_grow_chain((xs : \{lw}),(hd : \{ht}),(m : \{w}),(oldlim : Num)) == (if tlsf_used(hd(m)) { APPEND(xs,[(word(oldlim) : \{w})]) } else { xs })",
  )
  let params = "(d : \{w}),(s : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(before : \{heap}),(fp : \{rty})"
  let old = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let nt = "tlsf_grow_top((hd : \{ht}),(top : \{w}),(lim : Num))"
  let nx = "tlsf_grow_chain((xs : \{lw}),(hd : \{ht}),(top : \{w}),(lim : Num))"
  let nh = "tlsf_grow_headers((hd : \{ht}),(top : \{w}),(lim : Num),(ms : Num))"
  let grown = "tlsf_large((d : \{w}),(ms : Num),\{nt},\{nx},\{nh},(fl2 : \{w}),(sb2 : (Num) -> \{w}),(bl2 : \{bt}))"
  let client = "(fp : \{rty})((gs : List[Value]),(lim : Num))"
  def(
    "tlsf_ensure_pre",
    "tlsf_ensure_pre(\{params}) == ((args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [V_num(ConstInt32(s))] && 16 <= val(s) && val(s) <= 4160749568 && ms == lim && h == before && star(\{old},\{client},h))",
  )
  def(
    "tlsf_ensure_post",
    "tlsf_ensure_post(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (res == [V_num(ConstInt32((word(0) : \{w})))] && ms == lim && h == before && star(\{old},\{client},h)) || (res == [V_num(ConstInt32((word(1) : \{w})))] && ms == lim + val(tlsf_ensure_pages(s,hd(top)))*65536 && lim <= ms && ms <= 4294967296 && !tlsf_used((\{nh})(\{nt})) && val(tlsf_ensure_expected(s)) <= val(tlsf_size((\{nh})(\{nt}))) && (∃ fl2 : \{w}, ∃ sb2 : (Num) -> \{w}, ∃ bl2 : \{bt}, star(\{grown},\{client},h))))",
  )
}
