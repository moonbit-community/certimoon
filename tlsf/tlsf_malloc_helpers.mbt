// All three inlined attempts use five work locals. The first full_malloc
// attempt has the original request in an additional leading local.

///|
fn malloc_variant_names() -> Array[String] {
  ["try", "first", "retry"]
}

///|
fn malloc_locals(v : String, work : Array[String]) -> String {
  "[" +
  ((if v == "first" { ["(original : Value)"] } else { [] }) +
  work +
  (if v == "retry" { ["(original : Value)"] } else { [] })).join(",") +
  "]"
}

///|
fn malloc_i(x : String) -> String {
  "V_num(ConstInt32((" + x + " : " + w32 + ")))"
}

///|
fn malloc_part(v : String, kind : String) -> String {
  "tlsf_malloc_" +
  v +
  "_" +
  kind +
  "((d : " +
  w32 +
  "),(initialize_idx : Num),(page_idx : Num),(take_idx : Num),(ensure_idx : Num))"
}

///|
fn malloc_env_variables() -> Array[(String, String)] {
  [
    ("d", w32),
    ("initialize_idx", "Num"),
    ("page_idx", "Num"),
    ("take_idx", "Num"),
    ("ensure_idx", "Num"),
  ]
}

///|
fn malloc_ac() -> Array[@kernel.Thm] {
  [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
}

///|
fn malloc_publication_variables() -> Array[(String, String)] {
  [
    ("initialize_idx", "Num"),
    ("page_idx", "Num"),
    ("take_idx", "Num"),
    ("ensure_idx", "Num"),
    ("original", "Value"),
  ]
}

///|
fn malloc_publication_quantify(vs : Array[(String, String)]) -> String {
  page_quantify(malloc_publication_variables() + vs)
}

///|
fn malloc_publication_inst(
  th : @kernel.Thm,
  args : Array[String],
) -> @kernel.Thm raise {
  let extra = if @wasm.term_constants(@kernel.concl(th)).any(n => {
      [
        "tlsf_malloc_first_fresh", "tlsf_malloc_first_partial", "tlsf_malloc_first_head",
        "tlsf_malloc_retry_fresh", "tlsf_malloc_retry_partial", "tlsf_malloc_retry_head",
      ].contains(n)
    }) {
    malloc_publication_variables().map(v => "(" + v.0 + " : " + v.1 + ")")
  } else {
    []
  }
  inst(th, extra + args)
}

///|
fn malloc_suffix_locals(v : String, kind : String) -> String {
  let i = malloc_i
  let w = w32
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : List[" + w + "])"
  let head = "tlsf_small_head(" + bs + ")"
  let work = if kind == "cached" {
    [
      i("word_add(" + b + ",word(8))"),
      i("word((k : Num))"),
      i(head),
      "(l3 : Value)",
      "(l4 : Value)",
    ]
  } else {
    [
      i(
        if kind == "fresh" {
          p
        } else {
          "tlsf_small_head((z : List[" + w + "]))"
        },
      ),
      i(if kind == "fresh" { "word_add(" + b + ",word(8))" } else { b }),
      i("word((s : Num))"),
      i("word_add(" + p + ",word(20))"),
      i(head),
    ]
  }
  malloc_locals(v, work)
}
