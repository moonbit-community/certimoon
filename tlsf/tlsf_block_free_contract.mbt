// The compiler inlines Block::free in public free. Its entry locals are
// [any, block_header, any]; its administrative result is i32(0).

///|
fn block_model_args() -> Array[String] {
  page_model_variables().map(v => "(" + v.0 + " : " + v.1 + ")")
}

///|
fn block_pick(args : Array[String], indices : Array[Int32]) -> String {
  indices.map(i => args[i]).join(",")
}

///|
fn block_pages(args : Array[String]) -> String {
  "tlsf_small_pages_heap(" + block_pick(args, [8, 4, 9, 10, 11, 12]) + ")"
}

///|
fn block_table(args : Array[String]) -> String {
  "tlsf_small_table(" + block_pick(args, [0, 13, 14]) + ")"
}

///|
fn block_large(args : Array[String]) -> String {
  "tlsf_large(" + args[:8].to_owned().join(",") + ")"
}

///|
fn block_backing(args : Array[String]) -> String {
  "tlsf_small_backing(" + block_pick(args, [3, 4, 8, 9, 10, 11, 12, 1]) + ")"
}

///|
fn block_lists(args : Array[String]) -> String {
  "tlsf_small_lists_ok(" + block_pick(args, [8, 9, 10, 11, 12, 13, 14]) + ")"
}

///|
fn block_after_release(
  args : Array[String],
  p : String,
  b : String,
) -> Array[String] {
  let result = args.copy()
  result[10] = "tlsf_block_free_loc(" + args[10] + "," + p + "," + b + ")"
  result[12] = "tlsf_block_free_live(" + args[12] + "," + p + "," + b + ")"
  result
}

///|
fn block_after_free(
  args : Array[String],
  p : String,
  b : String,
) -> Array[String] {
  let result = block_after_release(args, p, b)
  result[8] = "tlsf_block_free_pages(" +
    block_pick(args, [8, 11, 12]) +
    "," +
    p +
    ")"
  result[14] = "tlsf_block_free_partial(" +
    block_pick(args, [14, 9, 11, 12]) +
    "," +
    p +
    ")"
  result
}

///|
fn block_rty(args : Array[String], fp : String) -> String {
  "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == " +
  args[1] +
  " && " +
  small_star([
    block_large(args),
    block_pages(args),
    block_table(args),
    "(" + fp + ")(gs,ms)",
  ]) +
  "(h)"
}

///|
fn define_tlsf_block_free_contract() -> Unit raise {
  let w = w32
  let model = page_model_variables()
  let vs = model +
    [("p", w), ("b", w), ("l0", "Value"), ("l2", "Value"), ("fp", rty)]
  let params = page_arguments(vs)
  let args = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let invariant = "tlsf_allocator(" + args.join(",") + ")"
  def(
    "tlsf_block_free_pre",
    "tlsf_block_free_pre(" +
    params +
    ") == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => vs == NIL && lc == [(l0 : Value)," +
    i(b) +
    ",(l2 : Value)] && ms == " +
    args[1] +
    " && MEM(" +
    p +
    "," +
    args[8] +
    ") && MEM(" +
    b +
    "," +
    args[12] +
    "(" +
    p +
    ")) && star(" +
    invariant +
    ",star(tlsf_bytes(val(" +
    b +
    ")+8," +
    args[9] +
    "(" +
    p +
    ")),(fp : " +
    rty +
    ")(gs,ms)),h))",
  )
  let updated = block_after_free(args, p, b)
  let worlds = model.filter(v => {
    ["top", "xs", "hd", "fl", "sb", "bl"].contains(v.0)
  })
  for index in 0..<model.length() {
    let v = model[index]
    if ["top", "xs", "hd", "fl", "sb", "bl"].contains(v.0) {
      updated[index] = "(" + v.0 + "2 : " + v.1 + ")"
    }
  }
  let exists = worlds.map(v => "∃ " + v.0 + "2 : " + v.1 + ", ").join("")
  def(
    "tlsf_block_free_post",
    "tlsf_block_free_post(" +
    params +
    ") == ((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => vs == [" +
    i("word(0)") +
    "] && ms == " +
    args[1] +
    " && (" +
    exists +
    "star(tlsf_allocator(" +
    updated.join(",") +
    "),(fp : " +
    rty +
    ")(gs,ms),h)))",
  )
}

///|
fn block_usage(args : Array[String], p : String) -> String {
  "tlsf_small_used(" + args[11] + "(" + p + ")," + args[12] + "(" + p + "))"
}

///|
fn block_total(args : Array[String], p : String) -> String {
  "tlsf_small_total(" + args[9] + "(" + p + "))"
}

///|
fn block_large_frame(args : Array[String], fp : String) -> String {
  "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == " +
  args[1] +
  " && star(" +
  block_large(args) +
  ",(" +
  fp +
  ")(gs,ms),h)"
}

///|
fn block_gate(args : Array[String], p : String) -> String {
  "if " +
  block_usage(args, p) +
  " < " +
  block_total(args, p) +
  " { emp } else { tlsf_bytes(val(" +
  p +
  ")+24,8) }"
}

///|
fn block_pending_rty(
  args : Array[String],
  p : String,
  b : String,
  fp : String,
) -> String {
  let current = block_after_release(args, p, b)
  "(gs : List[Value]) => (ms : Num) => " +
  small_star([
    block_pages(current),
    block_table(args),
    block_gate(args, p),
    "(" + block_large_frame(args, fp) + ")((gs : List[Value]),(ms : Num))",
  ])
}

///|
fn block_input_rty(
  args : Array[String],
  p : String,
  b : String,
  fp : String,
) -> String {
  "(gs : List[Value]) => (ms : Num) => " +
  small_star([
    block_pages(args),
    block_table(args),
    "tlsf_bytes(val(" + b + ")+8," + args[9] + "(" + p + "))",
    "(" + block_large_frame(args, fp) + ")((gs : List[Value]),(ms : Num))",
  ])
}
