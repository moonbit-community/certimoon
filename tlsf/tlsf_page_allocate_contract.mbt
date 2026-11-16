// A fresh page is an unpublished used TLSF memory. Existing stable pages
// retain their models; the caller must set used and publish the new slots.

///|
fn page_model_variables() -> Array[(String, String)] {
  let w = w32
  let lw = "List[\{w}]"
  [
    ("d", w),
    ("lim", "Num"),
    ("top", w),
    ("xs", lw),
    ("hd", "(" + w + ") -> " + w),
    ("fl", w),
    ("sb", "(Num) -> " + w),
    ("bl", "(Num) -> (Num) -> " + lw),
    ("ps", lw),
    ("sz", "(" + w + ") -> Num"),
    ("loc", "(" + w + ") -> " + lw),
    ("cached", "(" + w + ") -> " + lw),
    ("live", "(" + w + ") -> " + lw),
    ("fast", "(Num) -> " + lw),
    ("partial", "(Num) -> " + lw),
  ]
}

///|
fn page_quantify(vs : Array[(String, String)]) -> String {
  vs.map(v => "∀ \{v.0} : \{v.1}, ").join("")
}

///|
fn page_arguments(vs : Array[(String, String)]) -> String {
  vs.map(v => "(\{v.0} : \{v.1})").join(",")
}

///|
fn define_tlsf_page_allocate_contract() -> Unit raise {
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
  let pure = "!(p == word(0)) && !MEM(p,(ps : \{lw})) && MEM(p,(xs2 : \{lw})) && tlsf_used((hd2 : \{ht})(p)) && tlsf_retains((xs : \{lw}),(hd : \{ht}),xs2,hd2)"
  def(
    "tlsf_page_allocate_pre",
    "tlsf_page_allocate_pre(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [\{i("s")}] && \{legal} && ms == lim && h == (before : \{heap}) && star(\{old},\{client},h))",
  )
  let success = (fresh : Bool) => {
    let payload = if fresh {
      "tlsf_page_allocate_fresh((p : \{w}),val(tlsf_size((hd2 : \{ht})(p))),val((s : \{w})))"
    } else {
      "tlsf_bytes(val((p : \{w}))+8,val(tlsf_size((hd2 : \{ht})(p))))"
    }
    "\{exists}res == [\{i("p")}] && \{pure} && tlsf_page_allocate_geometry(p,val(tlsf_size(hd2(p))),val((s : \{w}))) && star(\{payload},star(tlsf_allocator(\{newargs},\{smallmodels}),\{client}),h)"
  }
  let failure = "res == [\{i("word(0)")}] && h == (before : \{heap}) && star(\{old},\{client},h)"
  def(
    "tlsf_page_allocate_reserved",
    "tlsf_page_allocate_reserved(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && ((\{failure}) || (\{success(false)})))",
  )
  def(
    "tlsf_page_allocate_post",
    "tlsf_page_allocate_post(\{params}) == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && ((\{failure}) || (\{success(true)})))",
  )
}
