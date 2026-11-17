///|
fn prove_tlsf_ensure_parts() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let defs = [
    "tlsf_ensure_code", "tlsf_ensure_prefix", "tlsf_ensure_used_amount", "tlsf_ensure_free_amount",
    "tlsf_ensure_guard", "tlsf_ensure_used_write", "tlsf_ensure_free_write", "tlsf_ensure_prefix_before_size",
    "tlsf_ensure_prefix_after_size", "tlsf_ensure_used_before_size", "tlsf_ensure_used_after_size",
    "tlsf_ensure_free_before_size", "tlsf_ensure_free_after_size",
  ].map(thm)
  let args = "(d : \{w}),(pop : Num),(push : Num)"
  for
    (name, left, a, b) in [
      (
        "tlsf_ensure_prefix_parts", "tlsf_ensure_prefix", "tlsf_ensure_prefix_before_size",
        "tlsf_ensure_prefix_after_size",
      ),
      (
        "tlsf_ensure_used_write_parts", "tlsf_ensure_used_write", "tlsf_ensure_used_before_size",
        "tlsf_ensure_used_after_size",
      ),
      (
        "tlsf_ensure_free_write_parts", "tlsf_ensure_free_write", "tlsf_ensure_free_before_size",
        "tlsf_ensure_free_after_size",
      ),
    ] {
    let _ = lemma(
      name,
      "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, \{left}(\{args}) == APPEND(\{a}(\{args}),CONS(Memory_size,\{b}(\{args})))",
      () => seq([gen, rw(defs + [@lists.append()])]),
    )
  }
  def(
    "tlsf_ensure_used_body",
    "tlsf_ensure_used_body(\{args}) == APPEND(tlsf_ensure_used_amount(d,pop,push),CONS(Memory_grow,APPEND(tlsf_ensure_guard(d,pop,push),APPEND(tlsf_ensure_used_write(d,pop,push),[Local_get(1),Call(push),Drop]))))",
  )
  def(
    "tlsf_ensure_free_body",
    "tlsf_ensure_free_body(\{args}) == APPEND(tlsf_ensure_free_amount(d,pop,push),CONS(Memory_grow,APPEND(tlsf_ensure_guard(d,pop,push),APPEND([Local_get(0),Call(pop)],APPEND(tlsf_ensure_free_write(d,pop,push),[Local_get(0),Call(push),Drop])))))",
  )
  let tail = "[If(Tbv(NONE),tlsf_ensure_used_body(\{args}),tlsf_ensure_free_body(\{args})),EConstNum(ConstInt32((word(1) : \{w})))]"
  let _ = lemma(
    "tlsf_ensure_code_parts",
    "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, tlsf_ensure_code(\{args}) == APPEND(tlsf_ensure_prefix(\{args}),\{tail})",
    () => {
      seq([
        gen,
        rw(
          defs +
          [
            thm("tlsf_ensure_used_body"),
            thm("tlsf_ensure_free_body"),
            @lists.append(),
          ],
        ),
      ])
    },
  )
}
