// The allocator's unused suffix starts at the aligned static-data end.
// Existing client assertions remain interpreted at the original memory size.

///|
fn define_tlsf_initialize_state() -> Unit raise {
  let w = w32
  let b = "Word[8]"
  def(
    "tlsf_initialize_pages",
    "tlsf_initialize_pages((d : \{w})) == DIV(val(tlsf_base(d)),65536)+DIV(MOD(val(tlsf_base(d)),65536)+67743,65536)",
  )
  def(
    "tlsf_initialize_required",
    "tlsf_initialize_required((d : \{w})) == word_add(word_jushr(tlsf_base(d),word(16)),word_jushr(word_add(word_and(tlsf_base(d),word(65535)),word(67743)),word(16)))",
  )
  def(
    "tlsf_initialize_limit",
    "tlsf_initialize_limit((d : \{w}),(lim : Num)) == MAX(lim,tlsf_initialize_pages(d)*65536)",
  )
  def(
    "tlsf_initialize_origin",
    "tlsf_initialize_origin((d : \{w})) == word_add(tlsf_base(d),word(2176))",
  )
  def(
    "tlsf_initialize_header",
    "tlsf_initialize_header((d : \{w}),(lim : Num)) == word_or(tlsf_capacity_at(lim,tlsf_initialize_origin(d)),word(2))",
  )
  def(
    "tlsf_initialize_headers",
    "tlsf_initialize_headers((d : \{w}),(lim : Num)) == ((x : \{w}) => tlsf_initialize_header(d,lim))",
  )
  def(
    "tlsf_initialize_zero",
    "tlsf_initialize_zero((d : \{w}),(lim : Num)) == pts(val(tlsf_base(d)),REPLICATE(lim-val(tlsf_base(d)),(word(0) : \{b})))",
  )
  def(
    "tlsf_initialize_valid",
    "tlsf_initialize_valid((d : \{w}),(lim : Num)) == (val(d) <= 4294965088 && val(tlsf_base(d)) <= lim && lim <= 4294967296 && MOD(lim,65536) == 0)",
  )
  let p = "(d : \{w}),(lim : Num),(before : \{heap}),(fp : \{rty})"
  let client = "(fp : \{rty})((gs : List[Value]),(lim : Num))"
  def(
    "tlsf_initialize_pre",
    "tlsf_initialize_pre(\{p}) == ((args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == NIL && tlsf_initialize_valid(d,lim) && ms == lim && h == before && star(tlsf_initialize_zero(d,lim),\{client},h))",
  )
  let m = "tlsf_initialize_origin((d : \{w}))"
  let hd = "tlsf_initialize_headers((d : \{w}),(ms : Num))"
  let hdr = "tlsf_initialize_header((d : \{w}),(ms : Num))"
  let zero = "((f : Num) => (word(0) : \{w}))"
  let empty = "((f : Num) => (j : Num) => (NIL : List[\{w}]))"
  let page_table = "pts(val(tlsf_base((d : \{w})))+1912,REPLICATE(264,(word(0) : \{b})))"
  let large = "tlsf_large((d : \{w}),(ms : Num),\{m},[\{m}],\{hd},tlsf_push_fl(\{hdr},word(0)),tlsf_push_sb(\{hdr},\{zero}),tlsf_push_bl(\{hdr},\{m},\{empty}))"
  def(
    "tlsf_initialize_post",
    "tlsf_initialize_post(\{p}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == NIL && ms == tlsf_initialize_limit(d,lim) && star(\{large},star(\{page_table},\{client}),h))",
  )
  def(
    "tlsf_initialize_abort",
    "tlsf_initialize_abort(\{p}) == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && h == before && star(tlsf_initialize_zero(d,lim),\{client},h))",
  )
}
