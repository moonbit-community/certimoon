// Stable equations for the three compiled branches. Keeping these separate
// avoids unfolding a model update while rewriting its usage arithmetic.

///|
fn prove_tlsf_block_free_model_cases() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let vars = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}"
  let u = "tlsf_small_used((cached : \{ls})((p : \{w})),(live : \{ls})(p))"
  let total = "tlsf_small_total((sz : (\{w}) -> Num)((p : \{w})))"
  let k = "DIV((sz : (\{w}) -> Num)((p : \{w})),8)"
  let pages = "tlsf_block_free_pages((ps : \{lw}),(cached : \{ls}),(live : \{ls}),(p : \{w}))"
  let part = "tlsf_block_free_partial((partial : (Num) -> \{lw}),(sz : (\{w}) -> Num),(cached : \{ls}),(live : \{ls}),(p : \{w}))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let defs = [thm("tlsf_block_free_pages"), thm("tlsf_block_free_partial")]
  let _ = lemma(
    "tlsf_block_free_model_full",
    "\{vars}, \{u} == \{total} && !(\{u} == 1) → \{pages} == ps && \{part} == tlsf_small_put_class(partial,\{k},CONS(p,partial(\{k})))",
    seq([
      gen,
      strip,
      free_have("!(\{total} == 1)", small_meson(ths([]))),
      arw(defs),
    ]),
  )
  let _ = lemma(
    "tlsf_block_free_model_partial",
    "\{vars}, !(\{u} == \{total}) && !(\{u} == 1) → \{pages} == ps && \{part} == partial",
    seq([gen, strip, arw(defs)]),
  )
  let _ = lemma(
    "tlsf_block_free_model_last",
    "\{vars}, \{u} == 1 && !(\{u} == \{total}) → \{pages} == tlsf_small_remove(p,ps) && \{part} == tlsf_small_put_class(partial,\{k},tlsf_small_remove(p,partial(\{k})))",
    seq([
      gen,
      strip,
      free_have("!((1 : Num) == \{total})", small_meson(ths([]))),
      arw(defs),
    ]),
  )
}
