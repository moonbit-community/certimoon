// Connect the compiled stores to contraction of a detached pair. The
// successor's previous word and the top pointer are repaired separately.

///|
fn prove_tlsf_free_merge_write() -> Unit raise {
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
  let hm = "\{hd}(\{m})"
  let hr = "\{hd}(\{r})"
  let nh = "tlsf_merge_headers(\{hd},\{m},\{r})"
  let z = "tlsf_merge_size(\{hm},\{hr})"
  let raw0 = "word_or(word_and(\{hm},word(3)),\{z})"
  let vars = "∀ ys : \{lw}, ∀ n : \{w}, ∀ ts : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l2 : Value, ∀ fp : \{rty}"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let other = if prev { m } else { r }
    let lc0 = "[\{i(active)},\{i(other)},(l2 : Value)]"
    let lc1 = "[\{i("m")},\{i(other)},\{i(hm)}]"
    for last in [true, false] {
      let zs = if last {
        "(NIL : \{lw})"
      } else {
        "CONS((n : \{w}),(ts : \{lw}))"
      }
      let nt = if last { m } else { "(top : \{w})" }
      let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},\{zs})))"
      let nx = "APPEND((ys : \{lw}),CONS(\{m},\{zs}))"
      let geom = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active})"
      let cond = "\{geom} && !tlsf_used(\{hm}) && !tlsf_used(\{hr}) && tlsf_bins_match(\{xs},tlsf_mark(tlsf_mark(\{hd},\{active}),\{other}),(bl : \{bt}))"
      let before = "tlsf_free_pair((d : \{w}),(top : \{w}),(ys : \{lw}),\{m},\{r},\{zs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
      let after = "tlsf_free_pending((d : \{w}),(lim : Num),\{nt},(ys : \{lw}),\{m},\{zs},\{nh},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
      let p = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{before},(fp : \{rty})(gs,ms),h)"
      let q = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{after},(fp : \{rty})(gs,ms),h)"
      let ps = [
        "tlsf_regions((word(0) : \{w}),(ys : \{lw}),\{hd})",
        cell(
          "word_add(\{m},word(4))",
          "tlsf_end((word(0) : " + w + "),(ys : " + lw + "))",
        ),
        "tlsf_bytes(val(\{m})+8,val(tlsf_size(\{hm})))",
        cell("word_add(\{r},word(4))", "m"),
        "tlsf_bytes(val(\{r})+8,val(tlsf_size(\{hr})))",
        "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
      ]
      if !last {
        ps.push(cell("tlsf_top_cell((d : " + w + "))", "top"))
        ps.push(cell("n", "\{hd}((n : \{w}))"))
        ps.push("tlsf_spare((n : \{w}),\{hd}(n))")
        ps.push("tlsf_regions((n : \{w}),(ts : \{lw}),\{hd})")
      }
      let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(ps)}(h)"
      let rawout = if last {
        "word_or(word_and(\{raw0},word(4294967293)),word(2))"
      } else {
        raw0
      }
      let heq = "\{rawout} == (\{nh})(\{m})"
      let side = "word_add(word_add(\{r},tlsf_size(\{hr})),word(12))"
      let sideeq = "\{side} == word_add((n : \{w}),word(4))"
      let rawname = "tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        (if last { "_last_write_raw" } else { "_next_write_raw" })
      let raw = inst(thm(rawname), [
        "(d : \{w})",
        "(pop : Num)",
        "(push : Num)",
        m,
        r,
        hm,
        hr,
        "(top : \{w})",
        "(l2 : Value)",
        frame,
      ])
      let raw = @simp.rewrite_rule(
        ths(
          [
            @equal.gsym(thm("tlsf_size")),
            @equal.gsym(thm("tlsf_merge_size")),
            @kernel.assume_rule(tm(heq)),
          ] +
          (if last { [] } else { [@kernel.assume_rule(tm(sideeq))] }),
        ),
      )(raw)
      let rt = args_of(@basics.dest_imp(@kernel.concl(raw)).1, "sl_triple", 3).unwrap()
      let lastcond = if last { "tlsf_last(\{hr})" } else { "!tlsf_last(\{hr})" }
      let bitcond = if last {
        "!(word_and(\{hr},word(2)) == word(0))"
      } else {
        "word_and(\{hr},word(2)) == word(0)"
      }
      let reverse = "∀ x : \{w}, MEM(x,APPEND((ys : \{lw}),\{zs})) → (\{nh})(x) == \{hd}(x)"
      let close = inst(thm("tlsf_free_merge_close"), [
        "(ys : \{lw})",
        zs,
        "(d : \{w})",
        "(lim : Num)",
        nt,
        m,
        r,
        hd,
        nh,
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "(fp : " + rty + ")((gs : List[Value]),(ms : Num))",
      ])
      let post = seq([
        gen,
        rw([thm("st")] + lift_rws()),
        strip,
        arw([]),
        @tactics.mp_tac(close),
        arw([]),
        @tactics.disch_then(th => {
          @tactics.match_mp_tac(@bool.spec(tm("(h : " + heap + ")"), th))
        }),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(
          [
            thm("tlsf_regions"),
            thm("tlsf_top_cell"),
            thm("star_assoc"),
            thm("star_comm"),
            thm("star_left_comm"),
          ] +
          lift_rws(),
        ),
      ])
      let pairfacts = seq([
        @tactics.mp_tac(
          inst(thm("tlsf_free_pair_facts"), [
            "(ys : \{lw})",
            zs,
            m,
            r,
            "(word(0) : \{w})",
            "tlsf_origin((d : \{w}))",
            "(lim : Num)",
            "(top : \{w})",
            hd,
          ]),
        ),
        @tactics.undisch_tac(tm(geom)),
        rw([thm("tlsf_free_geom_facts")]),
        strip,
        arw([]),
        strip,
      ])
      let sideproof = if last {
        @tactics.all_tac
      } else {
        seq([
          @tactics.mp_tac(
            inst(thm("tlsf_free_pair_facts"), [
              "APPEND((ys : \{lw}),[\{m}])",
              "(ts : \{lw})",
              r,
              "(n : \{w})",
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(lim : Num)",
              "(top : \{w})",
              hd,
            ]),
          ),
          arw([@equal.gsym(@lists.append_assoc()), @lists.append()]),
          strip,
          free_have(
            "(n : \{w}) == word_add(word_add(\{r},tlsf_size(\{hr})),word(8))",
            seq([@tactics.match_mp_tac(thm("tlsf_free_successor")), arw([])]),
          ),
          free_have(
            sideeq,
            seq([
              @tactics.match_mp_tac(thm("tlsf_free_successor_prev")),
              arw([]),
            ]),
          ),
        ])
      }
      let _ = lemma(
        "tlsf_free_merge_" +
        (if prev { "prev" } else { "next" }) +
        (if last { "_last" } else { "_interior" }),
        "\{vars}, \{cond} → sl_triple(st(NIL,\{lc0},\{p}),tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        "_write(d,pop,push),st(NIL,\{lc1},\{q}))",
        () => {
          seq([
            gen,
            strip,
            @tactics.mp_tac(
              inst(thm("tlsf_free_merge_model"), [
                "(ys : \{lw})",
                zs,
                m,
                r,
                active,
                "(d : \{w})",
                "(lim : Num)",
                "(top : \{w})",
                hd,
              ]),
            ),
            arw([@lists.not_cons_nil()]),
            strip,
            @tactics.mp_tac(
              inst(thm("tlsf_free_merge_bins"), [
                "(ys : \{lw})",
                zs,
                m,
                r,
                active,
                other,
                hd,
                "(bl : \{bt})",
              ]),
            ),
            arw([]),
            strip,
            free_have(
              reverse,
              seq([
                @tactics.x_gen_tac(tm("(x : \{w})")),
                @tactics.disch_tac,
                @meson.asm_meson_tac(ths([])),
              ]),
            ),
            pairfacts,
            free_have(
              "MOD(val(tlsf_size(\{hm})),8) == 0 && MOD(val(tlsf_size(\{hr})),8) == 0",
              seq([
                @tactics.undisch_tac(
                  tm("tlsf_block_ok(val(\{m}),(lim : Num),\{m},\{hd})"),
                ),
                @tactics.undisch_tac(
                  tm("tlsf_block_ok(val(\{r}),(lim : Num),\{r},\{hd})"),
                ),
                rw([thm("tlsf_block_ok")]),
                @meson.meson_tac(ths([])),
              ]),
            ),
            split_conjs(),
            @tactics.mp_tac(inst(thm("tlsf_merge_size_fields"), [hm, hr])),
            arw([]),
            strip,
            free_have(
              "val(word_add(\{r},word(4))) == val(\{r})+4",
              seq([
                @tactics.match_mp_tac(
                  inst(thm("tlsf_block_field_address"), [
                    "val(\{r})",
                    "(lim : Num)",
                    r,
                    hd,
                    "4",
                  ]),
                ),
                arw([]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
              ]),
            ),
            sideproof,
            if last {
              @tactics.all_tac
            } else {
              @tactics.pop_assum_list(all => {
                seq(
                  all
                  .to_array()
                  .filter(th => {
                    !@basics.aconv(
                      @kernel.concl(th),
                      tm(
                        "(n : \{w}) == word_add(word_add(\{r},tlsf_size(\{hr})),word(8))",
                      ),
                    )
                  })
                  .map(@tactics.assume_tac),
                )
              })
            },
            @tactics.rule_assum_tac(
              @simp.rewrite_rule(ths([@lists.not_cons_nil()])),
            ),
            free_have(
              bitcond,
              seq([@tactics.undisch_tac(tm(lastcond)), rw([thm("tlsf_last")])]),
            ),
            free_have(
              heq,
              seq([
                rw([thm("tlsf_merge_headers"), thm("tlsf_put")]),
                @tactics.match_mp_tac(
                  inst(
                    thm(
                      if last {
                        "tlsf_free_merge_store_last"
                      } else {
                        "tlsf_free_merge_store_next"
                      },
                    ),
                    [hm, hr],
                  ),
                ),
                arw([]),
              ]),
            ),
            @tactics.match_mp_tac(thm("sl_conseq")),
            @tactics.exists_tac(rt[0]),
            @tactics.exists_tac(rt[2]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                ent_tac(
                  [
                    thm("tlsf_free_pair"),
                    thm("tlsf_regions"),
                    thm("tlsf_top_cell"),
                  ],
                  [],
                ),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([seq([@tactics.match_mp_tac(raw), arw([])]), post]),
                ),
              ]),
            ),
          ])
        },
      )
    }
  }
}
