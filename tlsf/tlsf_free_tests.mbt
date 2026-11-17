// Lift the short-circuit tests through the physical-chain ownership view.

///|
fn prove_tlsf_free_tests() -> Unit raise {
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
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let lc = "[\{i("m")},(l1 : Value),(l2 : Value)]"
  let vars = "∀ ys : \{lw}, ∀ qs : \{lw}, ∀ zs : \{lw}, ∀ ts : \{lw}, ∀ m : \{w}, ∀ p : \{w}, ∀ n : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let no_neighbour = @wasm.compute_conv([])(
    tm("(wasm_bool((word(1) : \{w}) == word(0)) : \{w})"),
  )
  let pty = (ys : String, zs : String) => {
    "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),\{ys},\{m},\{zs},\{hd},(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  }
  let rty0 = (ys : String, zs : String) => {
    "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pty(ys,zs)},(fp : \{rty})(gs,ms),h)"
  }
  let shared = [
    thm("tlsf_free_pending"),
    thm("tlsf_regions_append"),
    thm("tlsf_regions"),
    thm("tlsf_free_end_append"),
    thm("tlsf_end"),
    thm("tlsf_top_cell"),
    thm("tlsf_used"),
    no_neighbour,
  ]
  for prev in [true, false] {
    for missing in [true, false] {
      let ys = if prev {
        if missing {
          "(NIL : \{lw})"
        } else {
          "APPEND((qs : \{lw}),[(p : \{w})])"
        }
      } else {
        "(ys : \{lw})"
      }
      let zs = if prev {
        "(zs : \{lw})"
      } else if missing {
        "(NIL : \{lw})"
      } else {
        "CONS((n : \{w}),(ts : \{lw}))"
      }
      let r0 = rty0(ys, zs)
      let ps = [
        cell("tlsf_top_cell((d : " + w + "))", "top"),
        cell("word_add(\{m},word(4))", "tlsf_end((word(0) : " + w + "),\{ys})"),
        "tlsf_bytes(val(\{m})+8,val(tlsf_size(\{hd}(\{m}))))",
        "tlsf_bins((d : \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))",
      ]
      if prev {
        ignore(ps.remove(1))
        ps.push(cell(m, "\{hd}(\{m})"))
        ps.push("tlsf_regions(\{m},\{zs},\{hd})")
        if !missing {
          ps.push("tlsf_regions((word(0) : \{w}),(qs : \{lw}),\{hd})")
          ps.push(
            cell(
              "word_add((p : " + w + "),word(4))",
              "tlsf_end((word(0) : " + w + "),(qs : " + lw + "))",
            ),
          )
          ps.push("tlsf_spare((p : \{w}),\{hd}(p))")
        }
      } else {
        ps.push("tlsf_regions((word(0) : \{w}),\{ys},\{hd})")
        if !missing {
          ps.push(cell("word_add((n : " + w + "),word(4))", "m"))
          ps.push("tlsf_spare((n : \{w}),\{hd}(n))")
          ps.push("tlsf_regions((n : \{w}),(ts : \{lw}),\{hd})")
        }
      }
      let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(ps)}(h)"
      let code = "tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        "_test(d,pop,push)"
      let rraw = "word_add(word_add(\{m},tlsf_size(\{hd}(\{m}))),word(8))"
      let cond = if prev {
        if missing {
          "T"
        } else {
          "!((p : \{w}) == word(0))"
        }
      } else if missing {
        "tlsf_last(\{hd}(\{m}))"
      } else {
        "!tlsf_last(\{hd}(\{m})) && (n : \{w}) == \{rraw}"
      }
      let inv = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),APPEND(\{ys},CONS(\{m},\{zs})),\{hd},\{m}) && !tlsf_used(\{hd}(\{m})) && tlsf_bins_match(APPEND(\{ys},CONS(\{m},\{zs})),tlsf_mark(\{hd},\{m}),(bl : \{bt}))"
      let cond = "(\{cond}) && (\{inv})"
      let raw = if prev {
        inst(
          thm(
            if missing {
              "tlsf_free_prev_zero_raw"
            } else {
              "tlsf_free_prev_nonzero_raw"
            },
          ),
          [
            "(d : \{w})",
            "(pop : Num)",
            "(push : Num)",
            m,
            if missing {
              "(word(0) : \{w})"
            } else {
              "\{hd}((p : \{w}))"
            },
            "(l1 : Value)",
            "(l2 : Value)",
            frame,
            if missing {
              "(word(0) : \{w})"
            } else {
              "(p : \{w})"
            },
          ],
        )
      } else {
        inst(
          thm(
            if missing {
              "tlsf_free_next_last_raw"
            } else {
              "tlsf_free_next_nonlast_raw"
            },
          ),
          [
            "(d : \{w})",
            "(pop : Num)",
            "(push : Num)",
            m,
            "\{hd}(\{m})",
            "(l1 : Value)",
            "(l2 : Value)",
            frame,
            if missing {
              "(word(0) : \{w})"
            } else {
              "\{hd}((n : \{w}))"
            },
          ],
        )
      }
      let raw = @simp.rewrite_rule(
        ths(
          [no_neighbour, @equal.gsym(thm("tlsf_size"))] +
          (if !prev && !missing {
            [@equal.sym(@kernel.assume_rule(tm("(n : \{w}) == \{rraw}")))]
          } else {
            []
          }),
        ),
      )(raw)
      let c = @kernel.concl(raw)
      let rt = args_of(
        if @basics.is_imp(c) {
          @basics.dest_imp(c).1
        } else {
          c
        },
        "sl_triple",
        3,
      ).unwrap()
      let stack = if missing {
        "[\{i("word(0)")}]"
      } else {
        "[\{i("wasm_bool(!tlsf_used(\{hd}("+(if prev { "(p : "+w+")" } else { "(n : "+w+")" })+")))")}]"
      }
      let lc1 = if prev {
        "[\{i("m")},\{i("word_add(\{m},word(4))")},(l2 : Value)]"
      } else {
        lc
      }
      let core = if @basics.is_imp(c) {
        seq([@tactics.match_mp_tac(raw), arw([])])
      } else {
        @tactics.accept_tac(raw)
      }
      let _ = lemma(
        "tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        (if missing { "_boundary_test" } else { "_neighbour_test" }),
        "\{vars}, \{cond} → sl_triple(st(NIL,\{lc},\{r0}),\{code},st(\{stack},\{lc1},\{r0}))",
        () => {
          seq([
            gen,
            strip,
            @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_used")]))),
            if prev || missing {
              @tactics.all_tac
            } else {
              free_have(
                "word_and(\{hd}(\{m}),word(2)) == word(0)",
                seq([
                  @tactics.undisch_tac(tm("!tlsf_last(\{hd}(\{m}))")),
                  rw([thm("tlsf_last")]),
                ]),
              )
            },
            if !prev && missing {
              free_have(
                "!(word_and(\{hd}(\{m}),word(2)) == word(0))",
                seq([
                  @tactics.undisch_tac(tm("tlsf_last(\{hd}(\{m}))")),
                  rw([thm("tlsf_last")]),
                ]),
              )
            } else {
              @tactics.all_tac
            },
            @tactics.match_mp_tac(thm("sl_conseq")),
            @tactics.exists_tac(rt[0]),
            @tactics.exists_tac(rt[2]),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                ent_tac(shared, []),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([core, ent_tac(shared, [])]),
                ),
              ]),
            ),
          ])
        },
      )
    }
  }
}
