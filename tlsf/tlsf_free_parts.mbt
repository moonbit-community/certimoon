///|
fn define_tlsf_free_parts() -> Unit raise {
  {
    let wat =
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev_args", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|local.tee 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_next_args", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|call push
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_publish", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _ = lemma(
    "tlsf_free_prev_body_parts",
    "∀ d : \{w32}, ∀ pop : Num, ∀ push : Num, tlsf_free_prev_body(d,pop,push) == APPEND(tlsf_free_prev_args(d,pop,push),APPEND([Call(pop)],tlsf_free_prev_write(d,pop,push)))",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(
          ths([
            thm("tlsf_free_prev_body"),
            thm("tlsf_free_prev_args"),
            thm("tlsf_free_prev_write"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_next_body_parts",
    "∀ d : \{w32}, ∀ pop : Num, ∀ push : Num, tlsf_free_next_body(d,pop,push) == APPEND(tlsf_free_next_args(d,pop,push),APPEND([Call(pop)],tlsf_free_next_write(d,pop,push)))",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(
          ths([
            thm("tlsf_free_next_body"),
            thm("tlsf_free_next_args"),
            thm("tlsf_free_next_write"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_prev_parts",
    "∀ d : \{w32}, ∀ pop : Num, ∀ push : Num, tlsf_free_prev(d,pop,push) == APPEND(tlsf_free_prev_test(d,pop,push),[If(Tbv(NONE),tlsf_free_prev_body(d,pop,push),NIL)])",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(
          ths([
            thm("tlsf_free_prev"),
            thm("tlsf_free_prev_test"),
            thm("tlsf_free_prev_body"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_next_parts",
    "∀ d : \{w32}, ∀ pop : Num, ∀ push : Num, tlsf_free_next(d,pop,push) == APPEND(tlsf_free_next_test(d,pop,push),[If(Tbv(NONE),tlsf_free_next_body(d,pop,push),NIL)])",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(
          ths([
            thm("tlsf_free_next"),
            thm("tlsf_free_next_test"),
            thm("tlsf_free_next_body"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_free_code_parts",
    "∀ d : \{w32}, ∀ pop : Num, ∀ push : Num, tlsf_free_code(d,pop,push) == APPEND(tlsf_free_clear(d,pop,push),APPEND(tlsf_free_prev(d,pop,push),APPEND(tlsf_free_next(d,pop,push),tlsf_free_publish(d,pop,push))))",
    () => {
      seq([
        gen,
        @simp.rewrite_tac(
          ths([
            thm("tlsf_free_code"),
            thm("tlsf_free_clear"),
            thm("tlsf_free_prev"),
            thm("tlsf_free_next"),
            thm("tlsf_free_publish"),
            @lists.append(),
          ]),
        ),
      ])
    },
  )
}
