///|
fn define_tlsf_malloc_take_contract() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let query = "tlsf_search(" + n + "," + a[5] + "," + a[6] + "," + a[7] + ")"
  let params = a + [n, "(before : " + heap + ")", fp]
  let failure = "res == [" +
    malloc_i("word(0)") +
    "] && " +
    query +
    " == word(0) && (" +
    malloc_frame(a, fp, "(before : " + heap + ")") +
    ")(gs,ms,h)"
  let success = "∃ m : " +
    w +
    ", !(m == word(0)) && res == [" +
    malloc_i("(m : " + w + ")") +
    "] && (m : " +
    w +
    ") == " +
    query +
    " && tlsf_malloc_result(" +
    a[0] +
    "," +
    n +
    "," +
    a[1] +
    "," +
    fp +
    ",word_add(m,word(8)))(gs,ms,h)"
  def(
    "tlsf_malloc_take_selected_post",
    "tlsf_malloc_take_selected_post(" +
    params.join(",") +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => ms == " +
    a[1] +
    " && ((" +
    failure +
    ") || (" +
    success +
    ")))",
  )
}
