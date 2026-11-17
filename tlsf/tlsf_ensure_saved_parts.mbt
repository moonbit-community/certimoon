///|
fn prove_tlsf_ensure_saved_parts() -> Unit raise {
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
  let h = "\{hd}(\{m})"
  let args = [
    d,
    "(lim : Num)",
    "(ys : \{lw})",
    m,
    hd,
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
  ]
  let frame = "tlsf_ensure_frame(\{args.join(",")})"
  let saved = "tlsf_ensure_saved(\{args.join(",")},(before : \{heap}))"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let facts = "tlsf_physical_ok(\{d},(lim : Num),\{m},\{xs},\{hd}) && tlsf_bins_match(\{xs},\{hd},(bl : \{bt}))"
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ ys : \{lw}, ∀ m : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}, ∀ before : \{heap}"
  let ro_eq = inst(thm("tlsf_ensure_ro_saved"), args + ["(before : \{heap})"])
  let ro_given = @bool.undisch(ro_eq)
  let prefix0 = inst(thm("tlsf_ensure_prefix_raw"), [
    d,
    m,
    h,
    "(lim : Num)",
    "(before : \{heap})",
    frame,
    "(s : \{w})",
    "(pop : Num)",
    "(push : Num)",
  ])
  let prefix = @simp.rewrite_rule(ths([ro_given]))(prefix0)
  let p_concl = @basics.dest_imp(@kernel.concl(prefix)).1
  let guards = inst(thm("tlsf_ensure_metadata_guards"), [
    "(ys : \{lw})",
    d,
    "(lim : Num)",
    m,
    hd,
  ])
  let _ = lemma(
    "tlsf_ensure_prefix_saved",
    "\{vars}, ∀ s : \{w}, ∀ pop : Num, ∀ push : Num, \{facts} → \{show(p_concl)}",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(prefix),
        @tactics.mp_tac(guards),
        arw([thm("tlsf_top_cell"), thm("tlsf_base")]),
      ])
    },
  )
  let free0 = inst(thm("tlsf_ensure_free_amount_raw"), [
    d,
    "(pop : Num)",
    "(push : Num)",
    m,
    "(e : \{w})",
    h,
    "(lim : Num)",
    "(before : \{heap})",
    frame,
  ])
  let free = @simp.rewrite_rule(ths([ro_given]))(free0)
  let _ = lemma(
    "tlsf_ensure_free_amount_saved",
    "\{vars}, ∀ e : \{w}, ∀ pop : Num, ∀ push : Num, \{facts} → \{show(@kernel.concl(free))}",
    () => seq([gen, strip, @tactics.accept_tac(free)]),
  )
  let large = "tlsf_large(\{d},(lim : Num),\{m},\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let client = "(fp : \{rty})((gs : List[Value]),(lim : Num))"
  let zero = "pts((lim : Num),REPLICATE((delta : Num),(word(0) : Word[8])))"
  let bare = "star(\{large},\{client})"
  let _ = lemma(
    "tlsf_ensure_saved_growth_frame",
    "\{vars}, ∀ delta : Num, ∀ gs : List[Value], ∀ heap0 : \{heap}, star(\{saved}(gs,lim),\{zero},heap0) → star(\{large},star(\{zero},\{client}),heap0)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_ensure_saved")]),
        @tactics.disch_tac,
        have(
          "star(\{bare},\{zero},(heap0 : \{heap}))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_star_forget_heap_eq"), [
                bare,
                zero,
                "(before : \{heap})",
                "(heap0 : \{heap})",
              ]),
            ),
            arw([]),
          ]),
        ),
        @tactics.first_x_assum(th => @tactics.mp_tac(th)),
        rw([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
      ])
    },
  )
}
