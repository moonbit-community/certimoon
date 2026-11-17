// Caller states immediately before the exact publication prefixes. A fresh
// page is the precise unpublished build returned by Page::allocate; a partial
// page is already a member of the combined invariant. All client bytes are fp.

///|
fn publish_vars() -> Array[(String, String)] {
  page_model_variables() +
  [
    ("p", w32),
    ("b", w32),
    ("bs", "List[" + w32 + "]"),
    ("s", "Num"),
    ("used0", w32),
    ("prev0", w32),
    ("l1", "Value"),
    ("l3", "Value"),
    ("l4", "Value"),
    ("fp", rty),
    ("z", "List[" + w32 + "]"),
  ]
}

///|
fn publish_ready(
  a : Array[String],
  p : String,
  b : String,
  bs : String,
  s : String,
  live : String,
) -> String {
  "tlsf_small_page_ok(" +
  [
    a[1],
    p,
    "val(tlsf_size(" + a[4] + "(" + p + ")))",
    s,
    "CONS(" + b + "," + bs + ")",
    "(NIL : List[" + w32 + "])",
    live,
  ].join(",") +
  ")"
}

///|
// These equations only abstract variables; no recursive definition is needed.
#callsite(autofill(loc))
fn page_publish_contract_def(
  name : String,
  s : String,
  loc~ : SourceLoc,
) -> Unit raise {
  let equation = tm(s)
  let th = @drule.new_definition(equation)
  @logic.record(name, th, kind="definition", loc~)
}

///|
fn define_tlsf_page_publish_contract() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let vs = publish_vars()
  let ps = page_arguments(vs)
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let i32 = (x : String) => "V_num(ConstInt32((" + x + " : " + w + ")))"
  for fresh in [true, false] {
    let tag = if fresh { "fresh" } else { "partial" }
    let n = publish_args(a, p, b, bs, s, fresh)
    let lc = if fresh {
      "[" +
      i32(p) +
      "," +
      i32(b) +
      "," +
      i32("word(" + s + ")") +
      "," +
      i32("word_add(" + p + ",word(20))") +
      ",(l4 : Value)]"
    } else {
      "[" +
      i32(p) +
      ",(l1 : Value)," +
      i32("word(" + s + ")") +
      ",(l3 : Value),(l4 : Value)]"
    }
    let extra = if fresh {
      [
        "tlsf_page_allocate_build(" +
        [
          p,
          cap,
          s,
          "tlsf_small_total(" + s + ")",
          "(used0 : " + w + ")",
          "(prev0 : " + w + ")",
        ].join(",") +
        ")",
      ]
    } else {
      []
    }
    let pure = if fresh {
      "!MEM(" +
      p +
      "," +
      a[8] +
      ") && MEM(" +
      p +
      "," +
      a[3] +
      ") && tlsf_used(" +
      a[4] +
      "(" +
      p +
      ")) && " +
      publish_ready(a, p, b, bs, s, "(NIL : " + lw + ")") +
      " && REVERSE(tlsf_small_slots(p,s,tlsf_small_total(s))) == CONS(b,bs)"
    } else {
      "MEM(" +
      p +
      "," +
      a[8] +
      ") && " +
      a[9] +
      "(" +
      p +
      ") == s && " +
      a[10] +
      "(" +
      p +
      ") == CONS(b,bs) && " +
      a[11] +
      "(" +
      p +
      ") == NIL && " +
      a[14] +
      "(DIV(s,8)) == CONS(p,(z : " +
      lw +
      "))"
    }
    page_publish_contract_def(
      "tlsf_page_publish_" + tag + "_pre",
      "tlsf_page_publish_" +
      tag +
      "_pre(" +
      ps +
      ") == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => vs == NIL && lc == " +
      lc +
      " && ms == (lim : Num) && " +
      pure +
      " && " +
      a[13] +
      "(DIV(s,8)) == NIL && " +
      small_star(
        ["tlsf_allocator(" + a.join(",") + ")"] +
        extra +
        ["(fp : " + rty + ")(gs,ms)"],
      ) +
      "(h))",
    )
    page_publish_contract_def(
      "tlsf_page_publish_" + tag + "_post",
      "tlsf_page_publish_" +
      tag +
      "_post(" +
      ps +
      ") == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
      heap +
      ") => vs == [" +
      i32("word_add(" + b + ",word(8))") +
      "] && ms == (lim : Num) && " +
      small_star([
        "tlsf_allocator(" + n.join(",") + ")",
        "tlsf_page_publish_payload(" + b + "," + s + ")",
        "(fp : " + rty + ")(gs,ms)",
      ]) +
      "(h))",
    )
  }
}
