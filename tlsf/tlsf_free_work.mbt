///|
fn define_tlsf_free_work() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  def(
    "tlsf_free_left",
    "tlsf_free_left((ys : \{lw}),(hd : \{ht})) == (ys == NIL || tlsf_used(hd(tlsf_end(word(0),ys))))",
  )
  def(
    "tlsf_free_right",
    "tlsf_free_right((zs : \{lw}),(hd : \{ht})) == (zs == NIL || tlsf_used(hd(HD(zs))))",
  )
  def(
    "tlsf_free_covers",
    "tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),(m : \{w}),(hd : \{ht})) == (val(m) <= val(m0) && val(m0)+8+val(tlsf_size(hd0(m0))) <= val(m)+8+val(tlsf_size(hd(m))))",
  )
  def(
    "tlsf_free_live",
    "tlsf_free_live((xs0 : \{lw}),(hd0 : \{ht}),(m0 : \{w}),(xs : \{lw}),(hd : \{ht})) == (∀ x : \{w}, MEM(x,xs0) && !(x == m0) && tlsf_used(hd0(x)) → MEM(x,xs) && hd(x) == hd0(x))",
  )
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),(m : \{w}),(zs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let pure = "tlsf_free_geom(d,lim,top,\{xs},hd,m) && !tlsf_used(hd(m)) && tlsf_bins_match(\{xs},tlsf_mark(hd,m),bl) && tlsf_free_covers(m0,hd0,m,hd) && tlsf_free_live(xs0,hd0,m0,\{xs},hd) && (!left || tlsf_free_left(ys,hd)) && (!right || tlsf_free_right(zs,hd))"
  def(
    "tlsf_free_work",
    "tlsf_free_work((d : \{w}),(lim : Num),(m0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fp : \{rty}),(left : Bool),(right : Bool)) == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == NIL && ms == lim && (∃ top : \{w}, ∃ ys : \{lw}, ∃ m : \{w}, ∃ zs : \{lw}, ∃ hd : \{ht}, ∃ fl : \{w}, ∃ sb : (Num) -> \{w}, ∃ bl : \{bt}, ∃ l1 : Value, ∃ l2 : Value, lc == [V_num(ConstInt32(m)),l1,l2] && \{pure} && star(\{pending},fp(gs,ms),h)))",
  )
}
