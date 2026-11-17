// The deterministic ghost update preserves the combined pure invariant in
// all three cases: partial release, full-to-partial, and page reclamation.

///|
fn prove_tlsf_block_free_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let model = page_model_variables()
  let vs = model + [("p", w), ("b", w)]
  let arg = (n : String) => {
    let v = vs.filter(v => v.0 == n)[0]
    "(" + v.0 + " : " + v.1 + ")"
  }
  let args = (names : Array[String]) => names.map(arg)
  let ba = args(["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"])
  let sa = args(["ps", "sz", "loc", "cached", "live", "fast", "partial"])
  let geometry = args([
    "xs", "hd", "ps", "sz", "loc", "cached", "live", "lim", "fast", "partial",
  ])
  let backing = "tlsf_small_backing(" + ba.join(",") + ")"
  let lists = "tlsf_small_lists_ok(" + sa.join(",") + ")"
  let pages = "tlsf_block_free_pages(" +
    args(["ps", "cached", "live", "p"]).join(",") +
    ")"
  let loc = "tlsf_block_free_loc(" + args(["loc", "p", "b"]).join(",") + ")"
  let live = "tlsf_block_free_live(" + args(["live", "p", "b"]).join(",") + ")"
  let part = "tlsf_block_free_partial(" +
    args(["partial", "sz", "cached", "live", "p"]).join(",") +
    ")"
  let nback = "tlsf_small_backing(" +
    [ba[0], ba[1], pages, ba[3], loc, ba[5], live, ba[7]].join(",") +
    ")"
  let nlists = "tlsf_small_lists_ok(" +
    [pages, sa[1], loc, sa[3], live, sa[5], part].join(",") +
    ")"
  let s = arg("sz") + "(" + arg("p") + ")"
  let u = "tlsf_small_used(" +
    arg("cached") +
    "(" +
    arg("p") +
    ")," +
    arg("live") +
    "(" +
    arg("p") +
    "))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_block_free_models",
    page_quantify(vs) +
    "\{backing} && \{lists} && MEM(p,ps) && MEM(b,live(p)) → \{nback} && \{nlists}",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(
                thm("tlsf_small_page_member_geometry"),
                geometry + [arg("p")],
              ),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(
              inst(
                thm("tlsf_small_live_release_usage"),
                geometry + args(["p", "b"]),
              ),
              g,
            ),
          )(g)
        },
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_capacity"), [s]), g),
          )(g)
        },
        @tactics.thenl(
          @class.asm_cases_tac(tm(u + " == 1")),
          @list.List([
            seq([
              free_have("!(\{u} == tlsf_small_total(\{s}))", @int.asm_arith_tac),
              free_have(
                "!((1 : Num) == tlsf_small_total(\{s}))",
                @int.asm_arith_tac,
              ),
              free_have(
                arg("cached") + "(" + arg("p") + ") == (NIL : " + lw + ")",
                small_meson(ths([])),
              ),
              rw([
                thm("tlsf_block_free_pages"),
                thm("tlsf_block_free_partial"),
                @kernel.assume_rule(tm(u + " == 1")),
                @kernel.assume_rule(
                  tm("!((1 : Num) == tlsf_small_total(" + s + "))"),
                ),
              ]),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_at(
                    "last backing",
                    free_apply(
                      inst(
                        thm("tlsf_small_backing_remove_page"),
                        geometry + args(["p", "b"]),
                      ),
                    ),
                  ),
                  free_at(
                    "last lists",
                    free_apply(
                      inst(
                        thm("tlsf_small_lists_release_last_class"),
                        geometry + args(["p", "b"]),
                      ),
                    ),
                  ),
                ]),
              ),
            ]),
            seq([
              rw([
                thm("tlsf_block_free_pages"),
                @kernel.assume_rule(tm("!(" + u + " == 1)")),
              ]),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_at(
                    "release backing",
                    free_apply(
                      inst(
                        thm("tlsf_small_backing_release"),
                        ba + args(["p", "b"]),
                      ),
                    ),
                  ),
                  seq([
                    @class.asm_cases_tac(
                      tm(u + " == tlsf_small_total(" + s + ")"),
                    ),
                    g => {
                      let branch = if g.0
                        .to_array()
                        .any(v => {
                          @basics.aconv(
                            @kernel.concl(v.1),
                            tm(u + " == tlsf_small_total(" + s + ")"),
                          )
                        }) {
                        u + " == tlsf_small_total(" + s + ")"
                      } else {
                        "!(" + u + " == tlsf_small_total(" + s + "))"
                      }
                      rw([
                        thm("tlsf_block_free_partial"),
                        @kernel.assume_rule(tm(branch)),
                        @kernel.assume_rule(tm("!(" + u + " == 1)")),
                      ])(g)
                    },
                    @tactics.first(
                      @list.List([
                        solve(
                          seq([
                            free_apply(
                              inst(
                                thm("tlsf_small_lists_release_full"),
                                sa + args(["p", "b"]),
                              ),
                            ),
                            small_meson(ths([])),
                          ]),
                        ),
                        solve(
                          seq([
                            free_have(
                              "1 < \{u} && \{u} < tlsf_small_total(\{s})",
                              @int.asm_arith_tac,
                            ),
                            free_at(
                              "partial lists",
                              free_apply(
                                inst(
                                  thm("tlsf_small_lists_release_partial"),
                                  sa + args(["p", "b"]),
                                ),
                              ),
                            ),
                            small_meson(ths([])),
                          ]),
                        ),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
