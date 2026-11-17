///|
fn small_star_parts(t : @kernel.Term) -> Array[@kernel.Term] {
  match args_of(t, "star", 2) {
    Some([a, b]) => small_star_parts(a) + small_star_parts(b)
    _ => [t]
  }
}

// Focus allocator-owned words while arbitrary client bytes stay in the frame.

///|
fn prove_tlsf_small_ownership() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hr"),
    thm("star_emp_hl"),
  ]
  let slot = "tlsf_small_slot((p : \{w}),(s : Num),(i : Num))"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let _ = lemma(
    "tlsf_small_live_owned",
    "∀ p : \{w}, ∀ s : Num, ∀ live : \{lw}, ∀ i : Num, MEM(\{slot},live) → tlsf_small_slot_heap(p,s,live,i) == star(\{cell("val("+slot+")","word(4)")},\{cell("val("+slot+")+4","(p : "+w+")")})",
    () => {
      seq([gen, @tactics.disch_tac, rw([thm("tlsf_small_slot_heap")]), arw(ac)])
    },
  )
  let _ = lemma(
    "tlsf_small_page_slot_focus",
    "∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ i : Num, i < tlsf_small_total(s) → (∃ rest : \{hprop}, tlsf_small_page_heap(p,cap,s,loc,cached,live) == star(tlsf_small_slot_heap(p,s,live,i),rest))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_small_page_heap")]),
        @tactics.mp_tac(
          inst(thm("tlsf_istar_focus"), [
            "tlsf_small_total((s : Num))",
            "tlsf_small_slot_heap((p : \{w}),(s : Num),(live : \{lw}))",
            "(i : Num)",
          ]),
        ),
        arw([]),
        @tactics.disch_then(th => @tactics.subst1_tac(th)),
        g => {
          let (_, body) = @basics.dest_exists(g.1)
          let target = args_of(@equal.rhs(body), "star", 2).unwrap()[0]
          let parts = small_star_parts(@equal.lhs(body))
          if !parts.any(t => @basics.aconv(t, target)) {
            raise Failure("small slot was not exposed")
          }
          let rest = small_star(
            parts.filter(t => !@basics.aconv(t, target)).map(show),
          )
          seq([@tactics.exists_tac(tm(rest)), rw(ac)])(g)
        },
      ])
    },
  )
  let ls = "(\{w}) -> \{lw}"
  let args = "(d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : (\{w}) -> \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : (Num) -> (Num) -> \{lw}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw})"
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : (\{w}) -> \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : (Num) -> (Num) -> \{lw}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}"
  let all = "tlsf_allocator(\{args})"
  let large = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : (\{w}) -> \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : (Num) -> (Num) -> \{lw}))"
  let small = "tlsf_small((d : \{w}),(hd : (\{w}) -> \{w}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw}))"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : (\{w}) -> \{w}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))"
  let _ = lemma(
    "tlsf_allocator_frame",
    "\{vars}, ∀ client : \{hprop}, star(\{all},client) == ((h : \{heap}) => \{backing} && star(\{large},star(\{small},client),h))",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_allocator"),
          thm("star_pure_hl"),
          thm("star_assoc"),
          @class.eta_ax(),
          @class.fun_eq_thm(),
        ]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_allocator_page_used",
    "\{vars}, ∀ client : \{hprop}, ∀ h : \{heap}, ∀ p : \{w}, star(\{all},client,h) && MEM(p,ps) → MEM(p,xs) && tlsf_used(hd(p)) && 1080 <= val(tlsf_size(hd(p)))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_allocator_frame")]),
        @meson.meson_tac(ths([thm("tlsf_small_backing_used")])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_allocator_page_not_in_bins",
    "\{vars}, ∀ client : \{hprop}, ∀ h : \{heap}, ∀ p : \{w}, ∀ f : Num, ∀ j : Num, star(\{all},client,h) && MEM(p,ps) && f < 28 && j < 16 → tlsf_count(p,bl(f)(j)) == 0",
    () => {
      seq([
        gen,
        rw([thm("tlsf_allocator_frame"), thm("tlsf_large"), thm("star_pure_hl")]),
        strip,
        free_have(
          "tlsf_used((hd : (\{w}) -> \{w})((p : \{w})))",
          seq([
            @tactics.undisch_tac(tm(backing)),
            rw([thm("tlsf_small_backing")]),
            small_meson(ths([])),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_bins_match_exact"), [
            "(xs : \{lw})",
            "(hd : (\{w}) -> \{w})",
            "(bl : (Num) -> (Num) -> \{lw})",
            "(p : \{w})",
            "(f : Num)",
            "(j : Num)",
          ]),
        ),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_allocator_client_write",
    "\{vars}, ∀ client : \{hprop}, ∀ a : Num, ∀ old : List[Word[8]], ∀ bytes : List[Word[8]], ∀ mem : (Limit_t,List[Word[8]]), star(\{all},star(pts(a,old),client),heap_of(mem)) && LENGTH(bytes) == LENGTH(old) && !(old == NIL) → star(\{all},star(pts(a,bytes),client),heap_of(write_bytes(mem,a,bytes)))",
    () => {
      seq([
        gen,
        strip,
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths(ac))),
        @tactics.mp_tac(
          inst(thm("write_pts"), [
            "(a : Num)",
            "(old : List[Word[8]])",
            "(bytes : List[Word[8]])",
            "star(\{all},(client : \{hprop}))",
            "(mem : (Limit_t,List[Word[8]]))",
          ]),
        ),
        arw(ac),
      ])
    },
  )
}
