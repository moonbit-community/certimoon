// Logical page accounting is independent of the physical order of slots.

///|
fn prove_tlsf_block_free_pure() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let v = "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ b : \{w}"
  let ok = "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let _ = lemma(
    "tlsf_small_page_release_ok",
    "\{v}, \{ok} && MEM(b,live) → tlsf_small_page_ok(lim,p,cap,s,CONS(b,loc),cached,tlsf_small_remove(b,live))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_page_ok")]),
        strip,
        arw([]),
        @tactics.mp_tac(
          inst(thm("tlsf_small_release_model"), [
            "(p : " + w + ")",
            "(s : Num)",
            "(b : " + w + ")",
            "(loc : " + lw + ")",
            "(cached : " + lw + ")",
            "(live : " + lw + ")",
          ]),
        ),
        arw([]),
        small_meson(ths([])),
      ])
    },
  )
  let ps = "(ps : \{lw})"
  let sz = "(sz : (\{w}) -> Num)"
  let lo = "(loc : \{ls})"
  let ca = "(cached : \{ls})"
  let li = "(live : \{ls})"
  let nl = "tlsf_block_free_loc(\{lo},(p : \{w}),(b : \{w}))"
  let nv = "tlsf_block_free_live(\{li},(p : \{w}),(b : \{w}))"
  let mv = "∀ xs : \{lw}, ∀ hd : (\{w}) -> \{w}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ p : \{w}, ∀ b : \{w}"
  let _ = lemma(
    "tlsf_small_backing_release",
    "\{mv}, tlsf_small_backing(xs,hd,\{ps},\{sz},\{lo},\{ca},\{li},lim) && MEM(p,ps) && MEM(b,live(p)) → tlsf_small_backing(xs,hd,ps,sz,\{nl},cached,\{nv},lim)",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_small_backing"),
          thm("tlsf_block_free_loc"),
          thm("tlsf_block_free_live"),
          thm("tlsf_small_put"),
        ]),
        strip,
        @tactics.x_gen_tac(tm("(q : " + w + ")")),
        @tactics.disch_tac,
        @tactics.first_x_assum(th => {
          @tactics.mp_tac(@bool.spec(tm("(q : " + w + ")"), th))
        }),
        arw([]),
        strip,
        @class.asm_cases_tac(tm("(q : " + w + ") == (p : " + w + ")")),
        subst_vars(),
        arw([]),
        @tactics.match_mp_tac(thm("tlsf_small_page_release_ok")),
        arw([]),
      ])
    },
  )
}
