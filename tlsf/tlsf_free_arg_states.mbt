///|
fn prove_tlsf_free_arg_states() -> Unit raise {
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
  let star = (ps : Array[String]) => {
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    out
  }
  let hd = "(hd : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},(zs : \{lw}))))"
  let vars = "∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let other = if prev { m } else { r }
    let ys0 = if prev { "APPEND((ys : \{lw}),[\{m}])" } else { "(ys : \{lw})" }
    let zs0 = if prev { "(zs : \{lw})" } else { "CONS(\{r},(zs : \{lw}))" }
    let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),\{ys0},\{active},\{zs0},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
    let p = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pending},(fp : \{rty})(gs,ms),h)"
    let lc0 = "[\{i(active)},(l1 : Value),(l2 : Value)]"
    let lc1 = "[\{i(active)},\{i(other)},(l2 : Value)]"
    let geom = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active})"
    let cond = "\{geom} && !tlsf_used(\{hd}(\{active})) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{active}),(bl : \{bt}))"
    let ps = [
      cell("tlsf_top_cell((d : " + w + "))", "top"),
      "tlsf_regions((word(0) : \{w}),\{ys0},\{hd})",
      "tlsf_bytes(val(\{active})+8,val(tlsf_size(\{hd}(\{active}))))",
      "tlsf_regions(\{active},\{zs0},\{hd})",
      "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
    ]
    if prev {
      ps.push(cell(active, "\{hd}(\{active})"))
    } else {
      ps.push(
        cell(
          "word_add(\{active},word(4))",
          "tlsf_end((word(0) : " + w + "),\{ys0})",
        ),
      )
    }
    let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(ps)}(h)"
    let rraw = "word_add(word_add(\{m},tlsf_size(\{hd}(\{m}))),word(8))"
    let eqr = "\{r} == \{rraw}"
    let raw = inst(
      thm(
        if prev {
          "tlsf_free_prev_args_raw"
        } else {
          "tlsf_free_next_args_raw"
        },
      ),
      [
        "(d : \{w})",
        "(pop : Num)",
        "(push : Num)",
        if prev {
          other
        } else {
          active
        },
        if prev {
          active
        } else {
          other
        },
        "\{hd}(\{active})",
        "(l1 : Value)",
        "(l2 : Value)",
        frame,
      ],
    )
    let raw = @simp.rewrite_rule(
      ths(
        [@class.eta_ax(), @equal.gsym(thm("tlsf_size"))] +
        (if prev { [] } else { [@equal.sym(@kernel.assume_rule(tm(eqr)))] }),
      ),
    )(raw)
    let rt = args_of(@kernel.concl(raw), "sl_triple", 3).unwrap()
    let rws = [
      thm("tlsf_free_pending"),
      thm("tlsf_regions_append"),
      thm("tlsf_regions"),
      thm("tlsf_free_end_append"),
      thm("tlsf_end"),
      thm("tlsf_top_cell"),
      @equal.gsym(@lists.append_assoc()),
      @lists.append(),
    ]
    let _ = lemma(
      "tlsf_free_" + (if prev { "prev" } else { "next" }) + "_arg_state",
      "\{vars}, \{cond} → sl_triple(st(NIL,\{lc0},\{p}),tlsf_free_" +
      (if prev { "prev" } else { "next" }) +
      "_args(d,pop,push),st([\{i(other)}],\{lc1},\{p}))",
      seq([
        gen,
        strip,
        if prev {
          @tactics.all_tac
        } else {
          seq([
            @tactics.mp_tac(
              inst(thm("tlsf_free_pair_facts"), [
                "(ys : \{lw})",
                "(zs : \{lw})",
                m,
                r,
                "(word(0) : \{w})",
                "tlsf_origin((d : \{w}))",
                "(lim : Num)",
                "(top : \{w})",
                hd,
              ]),
            ),
            @tactics.mp_tac(
              @simp.rewrite_rule(ths([thm("tlsf_free_geom_facts")]))(
                @kernel.assume_rule(tm(geom)),
              ),
            ),
            strip,
            arw([]),
            strip,
            free_have(
              eqr,
              seq([@tactics.match_mp_tac(thm("tlsf_free_successor")), arw([])]),
            ),
            @tactics.pop_assum_list(all => {
              seq(
                all
                .to_array()
                .filter(th => !@basics.aconv(@kernel.concl(th), tm(eqr)))
                .map(@tactics.assume_tac),
              )
            }),
          ])
        },
        @tactics.match_mp_tac(thm("sl_conseq")),
        @tactics.exists_tac(rt[0]),
        @tactics.exists_tac(rt[2]),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            ent_tac(rws, []),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([@tactics.accept_tac(raw), ent_tac(rws, [])]),
            ),
          ]),
        ),
      ]),
    )
  }
}
