// Extract contiguous pieces from the exact compiled bodies. The equations
// proved below check every extracted instruction against the existing code.

///|
fn define_tlsf_malloc_start_code() -> Unit raise {
  let params = malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
  for v in ["try", "first"] {
    let body = @basics.dest_list(malloc_program_code(malloc_part(v, "body"))).to_array()
    let prefix = @basics.dest_list(
      malloc_program_code(malloc_part(v, "ready_guard")),
    ).to_array()
    let offsets : Array[Int32] = []
    for i in 0..<(body.length() - prefix.length() + 1) {
      if body[i:i + prefix.length()].to_owned() == prefix {
        offsets.push(i)
      }
    }
    guard offsets is [start] else {
      raise Failure("startup: initialization guard must occur exactly once")
    }
    for
      (kind, code) in [
        ("start_head", body[:start].to_owned()),
        ("resume", body[start + prefix.length():].to_owned()),
      ] {
      ignore(
        program(
          "tlsf_malloc_" + v + "_" + kind,
          show(@lists.mk_list(@list.List(code), @kernel.type_of(body[0]))),
          params~,
        ),
      )
    }
    let _ = startup_lemma(
      "tlsf_malloc_" + v + "_start_parts",
      page_quantify(malloc_env_variables()) +
      malloc_part(v, "body") +
      " == APPEND(" +
      malloc_part(v, "start_head") +
      ",APPEND(" +
      malloc_part(v, "ready_guard") +
      "," +
      malloc_part(v, "resume") +
      "))",
      @simp.rewrite_tac(
        ths([
          thm("tlsf_malloc_" + v + "_body"),
          thm("tlsf_malloc_" + v + "_start_head"),
          thm("tlsf_malloc_" + v + "_ready_guard"),
          thm("tlsf_malloc_" + v + "_resume"),
          @lists.append(),
        ]),
      ),
    )
  }
  let full = @basics.dest_list(
    malloc_program_code("tlsf_full_malloc_code(" + params.join(",") + ")"),
  ).to_array()
  ignore(
    program(
      "tlsf_malloc_start_full_tail",
      show(
        @lists.mk_list(
          @list.List(full[1:].to_owned()),
          @kernel.type_of(full[0]),
        ),
      ),
      params~,
    ),
  )
  let _ = startup_lemma(
    "tlsf_malloc_start_full_parts",
    page_quantify(malloc_env_variables()) +
    "tlsf_full_malloc_code(" +
    params.join(",") +
    ") == APPEND(tlsf_malloc_full_prefix(" +
    params.join(",") +
    "),tlsf_malloc_start_full_tail(" +
    params.join(",") +
    "))",
    @simp.rewrite_tac(
      ths([
        thm("tlsf_full_malloc_code"),
        thm("tlsf_malloc_full_prefix"),
        thm("tlsf_malloc_start_full_tail"),
        @lists.append(),
      ]),
    ),
  )
  let ready = @basics.dest_list(
    malloc_program_code(malloc_part("try", "ready_guard")),
  ).to_array()
  for
    (kind, code) in [
      ("guard_test", ready[:ready.length() - 1].to_owned()),
      ("guard_call", ready[ready.length() - 1:].to_owned()),
    ] {
    ignore(
      program(
        "tlsf_malloc_start_" + kind,
        show(@lists.mk_list(@list.List(code), @kernel.type_of(ready[0]))),
        params~,
      ),
    )
  }
}
