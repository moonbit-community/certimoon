///|
fn prove_tlsf_ensure_posts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let vars = "∀ d : \{w}, ∀ s : \{w}, ∀ lim : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}"
  let args = [
    d,
    "(s : \{w})",
    "(lim : Num)",
    m,
    xs,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  let q = "tlsf_ensure_post(\{args.join(",")})"
  let saved = "tlsf_ensure_saved(\{d},(lim : Num),(ys : \{lw}),\{m},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(fp : \{rty}),(before : \{heap}))"
  let states = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let _ = lemma(
    "tlsf_ensure_failure_post",
    "\{vars}, \{states}, \{saved}(gs,ms,h) → \{q}([\{i("word(0)")}],gs,ms,h)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_ensure_saved"), thm("tlsf_ensure_post")]),
        strip,
        @tactics.disj1_tac,
        arw([]),
      ])
    },
  )
  let pages = "tlsf_ensure_pages((s : \{w}),\{hd}(\{m}))"
  let newlim = "(lim : Num)+val(\{pages})*65536"
  let nt = "tlsf_grow_top(\{hd},\{m},(lim : Num))"
  let nx = "tlsf_grow_chain(\{xs},\{hd},\{m},(lim : Num))"
  let nh = "tlsf_grow_headers(\{hd},\{m},(lim : Num),(ms : Num))"
  let large = "tlsf_large(\{d},(ms : Num),\{nt},\{nx},\{nh},(fl2 : \{w}),(sb2 : (Num) -> \{w}),(bl2 : \{bt}))"
  let cond = "tlsf_physical_ok(\{d},(lim : Num),\{m},\{xs},\{hd}) && 16 <= val((s : \{w})) && val(s) <= 4160749568 && DIV(lim,65536)+val(\{pages}) <= 65536 && ms == \{newlim} && star(\{large},(fp : \{rty})(gs,lim),h)"
  let _ = lemma(
    "tlsf_ensure_success_post",
    "\{vars}, ∀ fl2 : \{w}, ∀ sb2 : (Num) -> \{w}, ∀ bl2 : \{bt}, \{states}, \{cond} → \{q}([\{i("word(1)")}],gs,ms,h)",
    () => {
      seq([
        gen,
        strip,
        subst_vars(),
        @tactics.mp_tac(
          inst(thm("tlsf_ensure_growth_fit"), [
            "(ys : \{lw})",
            d,
            "(s : \{w})",
            "(lim : Num)",
            m,
            hd,
          ]),
        ),
        arw([]),
        strip,
        rw([thm("tlsf_ensure_post")]),
        @tactics.disj2_tac,
        arw([]),
        @tactics.exists_tac(tm("(fl2 : \{w})")),
        @tactics.exists_tac(tm("(sb2 : (Num) -> \{w})")),
        @tactics.exists_tac(tm("(bl2 : \{bt})")),
        arw([]),
      ])
    },
  )
}
