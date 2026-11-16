// An unpublished fresh page owns its whole TLSF payload. The shipped code
// does not initialize used or prev; these words are carried as arbitrary
// values until the caller publishes the page and sets used to total.

///|
fn define_tlsf_page_allocate_state() -> Unit raise {
  let w = w32
  let p = "(p : \{w})"
  let s = "(s : Num)"
  let k = "(k : Num)"
  let slot = "tlsf_small_slot(\{p},\{s},(i : Num))"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  def(
    "tlsf_page_allocate_head",
    "tlsf_page_allocate_head(\{p},\{s},\{k}) == (if k == 0 { word(0) } else { tlsf_small_slot(p,s,k-1) })",
  )
  let item = small_star([
    cell("val(" + slot + ")", "word(4)"),
    cell("val(" + slot + ")+4", p),
    cell("val(" + slot + ")+8", "tlsf_page_allocate_head(p,s,i)"),
    "tlsf_bytes(val(\{slot})+12,s-4)",
  ])
  def(
    "tlsf_page_allocate_slot",
    "tlsf_page_allocate_slot(\{p},\{s},(i : Num)) == \{item}",
  )
  let fields = [
    cell("val(p)+8", "word(s)"),
    cell("val(p)+12", "word(tlsf_small_total(s))"),
    cell("val(p)+16", "used0"),
    cell("val(p)+20", "tlsf_page_allocate_head(p,s,k)"),
    cell("val(p)+24", "prev0"),
    cell("val(p)+28", "word(0)"),
    "tlsf_istar(tlsf_page_allocate_slot(p,s),k)",
    "tlsf_bytes(val(p)+32+(8+s)*k,(cap : Num)-24-(8+s)*k)",
  ]
  def(
    "tlsf_page_allocate_build",
    "tlsf_page_allocate_build(\{p},(cap : Num),\{s},\{k},(used0 : \{w}),(prev0 : \{w})) == \{small_star(fields)}",
  )
  def(
    "tlsf_page_allocate_geometry",
    "tlsf_page_allocate_geometry(\{p},(cap : Num),\{s}) == (!(p == word(0)) && MOD(val(p),8) == 0 && val(p)+8+cap <= 4294967296 && 1080 <= cap && 8 <= s && s <= 256 && MOD(s,8) == 0)",
  )
  def(
    "tlsf_page_allocate_fresh",
    "tlsf_page_allocate_fresh(\{p},(cap : Num),\{s}) == ((h : \{heap}) => tlsf_page_allocate_geometry(p,cap,s) && (∃ used0 : \{w}, ∃ prev0 : \{w}, tlsf_page_allocate_build(p,cap,s,tlsf_small_total(s),used0,prev0,h)))",
  )
}

///|
fn prove_tlsf_page_allocate_parts() -> Unit raise {
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let _ = lemma(
    "tlsf_page_allocate_parts",
    "∀ take_idx : Num, tlsf_page_allocate_code(take_idx) == APPEND(tlsf_page_allocate_call(take_idx),APPEND(tlsf_page_allocate_guard(take_idx),APPEND(tlsf_page_allocate_begin(take_idx),APPEND(tlsf_page_allocate_loop(take_idx),[Local_get(1)]))))",
    rw([
      thm("tlsf_page_allocate_code"),
      thm("tlsf_page_allocate_call"),
      thm("tlsf_page_allocate_guard"),
      thm("tlsf_page_allocate_begin"),
      thm("tlsf_page_allocate_loop"),
      @lists.append(),
    ]),
  )
}
