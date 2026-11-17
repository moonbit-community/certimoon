///|
fn prove_tlsf_free_begin() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let hd = "(hd : \{ht})"
  let nh = "tlsf_release(\{hd},(m : \{w}))"
  let large = "tlsf_large((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),(m : \{w}),(zs : \{lw}),\{nh},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let bytes = "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size(\{hd}(m))))"
  let client = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  let before = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{large},star(\{bytes},\{client}),h)"
  let after = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pending},\{client},h)"
  let lc = "[\{i("m")},(l1 : Value),(l2 : Value)]"
  let ps = [
    cell("tlsf_top_cell((d : " + w + "))", "top"),
    "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
    cell(
      "word_add((m : " + w + "),word(4))",
      "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
    ),
    bytes,
    "tlsf_regions((m : \{w}),(zs : \{lw}),\{hd})",
    "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
  ]
  let mut framed = client
  for k = ps.length() - 1; k >= 0; k = k - 1 {
    framed = "star(\{ps[k]},\{framed})"
  }
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{framed}(h)"
  let raw = inst(thm("tlsf_free_clear_raw"), [
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(m : \{w})",
    "\{hd}((m : \{w}))",
    "(l1 : Value)",
    "(l2 : Value)",
    frame,
  ])
  let old = "tlsf_physical_ok((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd})"
  let cond = "\{old} && tlsf_used(\{hd}((m : \{w}))) && tlsf_bins_match(\{xs},\{hd},(bl : \{bt}))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let rws = [
    thm("tlsf_large"),
    thm("tlsf_chain"),
    thm("tlsf_top_cell"),
    thm("tlsf_regions_append"),
    thm("tlsf_regions"),
    thm("tlsf_spare"),
    thm("tlsf_free_pending"),
    @simp.rewrite_conv(ths([thm("tlsf_release"), thm("tlsf_put")]))(
      tm("(\{nh})((m : \{w}))"),
    ),
    thm("tlsf_release_fields"),
  ]
  let _ = lemma(
    "tlsf_free_begin",
    "\{vars}, \{cond} → sl_triple(st(NIL,\{lc},\{before}),tlsf_free_clear(d,pop,push),st(NIL,\{lc},\{after}))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_free_begin_model"), [
            xs,
            "(m : \{w})",
            "(d : \{w})",
            "(lim : Num)",
            "(top : \{w})",
            hd,
            "(bl : \{bt})",
          ]),
        ),
        arw([]),
        strip,
        free_have(
          "!MEM((m : \{w}),(ys : \{lw})) && !MEM(m,(zs : \{lw}))",
          seq([
            @tactics.undisch_tac(tm(old)),
            rw([thm("tlsf_physical_ok")]),
            strip,
            @tactics.match_mp_tac(
              inst(thm("tlsf_focus_distinct"), [
                "(ys : \{lw})",
                "(zs : \{lw})",
                "(m : \{w})",
                "(word(0) : \{w})",
                "tlsf_origin((d : \{w}))",
                "(lim : Num)",
                "(top : \{w})",
                hd,
              ]),
            ),
            arw([]),
          ]),
        ),
        split_conjs(),
        seq(
          [("(ys : \{lw})", "(word(0) : \{w})"), ("(zs : \{lw})", "(m : \{w})")].map(pair => {
              let (ls, p) = pair
              free_have(
                "tlsf_regions(\{p},\{ls},\{nh}) == tlsf_regions(\{p},\{ls},\{hd})",
                seq([
                  @tactics.match_mp_tac(
                    inst(thm("tlsf_regions_cong"), [ls, p, nh, hd]),
                  ),
                  @tactics.x_gen_tac(tm("(x : \{w})")),
                  @tactics.disch_tac,
                  free_have(
                    "!((x : \{w}) == (m : \{w}))",
                    @meson.asm_meson_tac(ths([])),
                  ),
                  arw([thm("tlsf_release"), thm("tlsf_put")]),
                ]),
              )
            },
          ),
        ),
        by_path(raw, "T", rws, [], rws, []),
      ])
    },
  )
}
