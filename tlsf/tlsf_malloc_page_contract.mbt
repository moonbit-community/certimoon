///|
fn define_tlsf_malloc_page_contract() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let model = page_model_variables()
  let args = page_arguments(model)
  let smallmodels = page_arguments(model[8:].to_owned())
  let old = "tlsf_allocator(\{args})"
  let client = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  let params = "\{args},(s : \{w}),(before : \{heap}),(fp : \{rty})"
  let legal = "8 <= val(s) && val(s) <= 256 && MOD(val(s),8) == 0"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let newargs = "(d : \{w}),(lim : Num),(top2 : \{w}),(xs2 : \{lw}),(hd2 : \{ht}),(fl2 : \{w}),(sb2 : (Num) -> \{w}),(bl2 : \{bt})"
  let exists = "∃ p : \{w}, ∃ top2 : \{w}, ∃ xs2 : \{lw}, ∃ hd2 : \{ht}, ∃ fl2 : \{w}, ∃ sb2 : (Num) -> \{w}, ∃ bl2 : \{bt}, "
  let pure = "!(tlsf_search((word(1080) : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt})) == word(0)) && !(p == word(0)) && !MEM(p,(ps : \{lw})) && MEM(p,(xs2 : \{lw})) && tlsf_used((hd2 : \{ht})(p)) && tlsf_retains((xs : \{lw}),(hd : \{ht}),xs2,hd2)"
  def(
    "tlsf_malloc_page_pre",
    "tlsf_malloc_page_pre(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [\{i("s")}] && \{legal} && ms == lim && h == (before : \{heap}) && star(\{old},\{client},h))",
  )
  let success = (fresh : Bool) => {
    let payload = if fresh {
      "tlsf_page_allocate_fresh((p : \{w}),val(tlsf_size((hd2 : \{ht})(p))),val((s : \{w})))"
    } else {
      "tlsf_bytes(val((p : \{w}))+8,val(tlsf_size((hd2 : \{ht})(p))))"
    }
    "\{exists}res == [\{i("p")}] && \{pure} && tlsf_page_allocate_geometry(p,val(tlsf_size(hd2(p))),val((s : \{w}))) && star(\{payload},star(tlsf_allocator(\{newargs},\{smallmodels}),\{client}),h)"
  }
  let failure = "tlsf_search((word(1080) : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt})) == word(0) && res == [\{i("word(0)")}] && h == (before : \{heap}) && star(\{old},\{client},h)"
  def(
    "tlsf_malloc_page_reserved",
    "tlsf_malloc_page_reserved(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && ((\{failure}) || (\{success(false)})))",
  )
  def(
    "tlsf_malloc_page_post",
    "tlsf_malloc_page_post(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && ((\{failure}) || (\{success(true)})))",
  )
}
