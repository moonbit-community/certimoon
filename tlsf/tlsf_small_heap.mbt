// Spatial ownership follows the shipped layout. Live payloads, including
// their first word, are omitted; free payloads own a next link and spare bytes.

///|
fn small_star(ps : Array[String]) -> String {
  let mut result = "emp"
  for i = ps.length() - 1; i >= 0; i = i - 1 {
    result = "star(\{ps[i]},\{result})"
  }
  result
}

///|
fn define_tlsf_small_heap() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let hd = "(hd : (\{w}) -> \{w})"
  let sz = "(sz : (\{w}) -> Num)"
  let lo = "(loc : \{ls})"
  let ca = "(cached : \{ls})"
  let li = "(live : \{ls})"
  let fast = "(fast : (Num) -> \{lw})"
  let part = "(partial : (Num) -> \{lw})"
  let p = "(p : \{w})"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  def(
    "tlsf_small_head",
    "tlsf_small_head((xs : \{lw})) == (if xs == NIL { word(0) } else { HD(xs) })",
  )
  def(
    "tlsf_small_links",
    "tlsf_small_links((NIL : \{lw})) == emp && tlsf_small_links(CONS((b : \{w}),bs)) == star(\{cell("val(b)+8","tlsf_small_head(bs)")},tlsf_small_links(bs))",
  )
  def(
    "tlsf_small_partial_links",
    "tlsf_small_partial_links((prev : \{w}),(NIL : \{lw})) == emp && tlsf_small_partial_links(prev,CONS((p : \{w}),ps)) == star(\{cell("val(p)+24","prev")},star(\{cell("val(p)+28","tlsf_small_head(ps)")},tlsf_small_partial_links(p,ps)))",
  )
  let slot = "tlsf_small_slot(\{p},(s : Num),(i : Num))"
  let slotbody = small_star([
    cell("val(" + slot + ")", "word(4)"),
    cell("val(" + slot + ")+4", p),
    "if MEM(\{slot},(live : \{lw})) { emp } else { tlsf_bytes(val(\{slot})+12,s-4) }",
  ])
  def(
    "tlsf_small_slot_heap",
    "tlsf_small_slot_heap(\{p},(s : Num),(live : \{lw}),(i : Num)) == \{slotbody}",
  )
  let used = "tlsf_small_used((cached : \{lw}),(live : \{lw}))"
  let total = "tlsf_small_total((s : Num))"
  let page = small_star([
    cell("val(p)+8", "word(s)"),
    cell("val(p)+12", "word(" + total + ")"),
    cell("val(p)+16", "word(" + used + ")"),
    cell("val(p)+20", "tlsf_small_head((loc : " + lw + "))"),
    "if \{used} < \{total} { emp } else { tlsf_bytes(val(p)+24,8) }",
    "tlsf_istar(tlsf_small_slot_heap(p,s,(live : \{lw})),\{total})",
    "tlsf_small_links((loc : \{lw}))",
    "tlsf_bytes(val(p)+32+(8+s)*\{total},(cap : Num)-24-(8+s)*\{total})",
  ])
  def(
    "tlsf_small_page_heap",
    "tlsf_small_page_heap(\{p},(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) == \{page}",
  )
  def(
    "tlsf_small_pages_heap",
    "tlsf_small_pages_heap((NIL : \{lw}),\{hd},\{sz},\{lo},\{ca},\{li}) == emp && tlsf_small_pages_heap(CONS(\{p},ps),hd,sz,loc,cached,live) == star(tlsf_small_page_heap(p,val(tlsf_size(hd(p))),sz(p),loc(p),cached(p),live(p)),tlsf_small_pages_heap(ps,hd,sz,loc,cached,live))",
  )
  let item = small_star([
    cell(
      "val(tlsf_base((d : " + w + ")))+1912+8*(j : Num)",
      "tlsf_small_head(" + fast + "(j))",
    ),
    cell(
      "val(tlsf_base((d : " + w + ")))+1916+8*(j : Num)",
      "tlsf_small_head(" + part + "(j))",
    ),
    "tlsf_small_links(\{fast}(j))",
    "tlsf_small_partial_links(word(0),\{part}(j))",
  ])
  def(
    "tlsf_small_table_item",
    "tlsf_small_table_item((d : \{w}),\{fast},\{part},(j : Num)) == \{item}",
  )
  def(
    "tlsf_small_table",
    "tlsf_small_table((d : \{w}),\{fast},\{part}) == tlsf_istar(tlsf_small_table_item(d,fast,partial),33)",
  )
  let ps = "(ps : \{lw})"
  let models = "\{ps},\{sz},\{lo},\{ca},\{li},\{fast},\{part}"
  def(
    "tlsf_small",
    "tlsf_small((d : \{w}),\{hd},\{models}) == ((h : \{heap}) => tlsf_small_lists_ok(\{models}) && star(tlsf_small_pages_heap(ps,hd,sz,loc,cached,live),tlsf_small_table(d,fast,partial),h))",
  )
  let largeargs = "(d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : (Num) -> (Num) -> \{lw})"
  def(
    "tlsf_allocator",
    "tlsf_allocator(\{largeargs},\{models}) == ((h : \{heap}) => tlsf_small_backing(xs,hd,ps,sz,loc,cached,live,lim) && star(tlsf_large(d,lim,top,xs,hd,fl,sb,bl),tlsf_small(d,hd,ps,sz,loc,cached,live,fast,partial),h))",
  )
}
