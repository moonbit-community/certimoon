// After unlinking a page with no live or cached blocks, recover its entire
// TLSF payload. Every byte in the separate client frame remains separate.

///|
fn prove_tlsf_block_free_recover_page() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let args = [
    "(lim : Num)",
    "(p : " + w + ")",
    "(cap : Num)",
    "(s : Num)",
    "(loc : " + lw + ")",
    "(NIL : " + lw + ")",
    "(NIL : " + lw + ")",
  ]
  let ok = "tlsf_small_page_ok(" + args.join(",") + ")"
  let total = "tlsf_small_total((s : Num))"
  let stride = "8+(s : Num)"
  let len = "(8+(s : Num))*\{total}"
  let b = "tlsf_small_slot((p : \{w}),(s : Num),(i : Num))"
  let slot = "tlsf_small_slot_heap((p : \{w}),(s : Num),(NIL : \{lw}))"
  let link = "(i : Num) => tlsf_bytes(val(\{b})+8,4)"
  let links = "tlsf_istar((\{link}),\{total})"
  let slots = "tlsf_istar(\{slot},\{total})"
  let pair = "(i : Num) => star(tlsf_bytes(val(\{b})+8,4),\{slot}(i))"
  let both = "tlsf_istar((\{pair}),\{total})"
  let bytes = "(i : Num) => tlsf_bytes(val(\{b}),\{stride})"
  let array = "tlsf_istar((\{bytes}),\{total})"
  let cell = (k : Int32, v : String) => {
    "pts(val((p : \{w}))+\{k},serialise_i32((\{v} : \{w})))"
  }
  let rest = small_star([
    cell(8, "word((s : Num))"),
    cell(12, "word(" + total + ")"),
    cell(16, "word(0)"),
    cell(20, "tlsf_small_head((loc : " + lw + "))"),
    cell(24, "prev"),
    cell(28, "next"),
    "tlsf_bytes(val((p : \{w}))+32+\{len},(cap : Num)-24-\{len})",
    "(R : " + hprop + ")",
  ])
  let page = "tlsf_small_page_heap((p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(NIL : \{lw}),(NIL : \{lw}))"
  let pre = "star(\{page},star(\{cell(24,"prev")},star(\{cell(28,"next")},(R : \{hprop}))), (h : \{heap}))"
  let post = "star(tlsf_bytes(val((p : \{w}))+8,(cap : Num)),(R : \{hprop}),(h : \{heap}))"
  let _ = lemma(
    "tlsf_small_recover_page",
    "∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ prev : \{w}, ∀ next : \{w}, ∀ R : \{hprop}, \{ok} → (∀ h : \{heap}, \{pre} → \{post})",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        free_have(
          "8 <= (s : Num) && (s : Num) <= 256 && 1080 <= (cap : Num)",
          seq([
            @tactics.undisch_tac(tm(ok)),
            rw([thm("tlsf_small_page_ok")]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_capacity"), ["(s : Num)"]), g),
          )(g)
        },
        free_have(
          "0 < \{total} && 24 <= (cap : Num) && \{len} <= cap-24 && cap-24 == \{len}+(cap-24-\{len})",
          @int.asm_arith_tac,
        ),
        free_have(
          "\{len}+((cap : Num)-24-\{len}) == cap-24",
          @int.asm_arith_tac,
        ),
        @tactics.x_gen_tac(tm("(h : " + heap + ")")),
        @tactics.disch_tac,
        free_have(
          "star(tlsf_small_links((loc : \{lw})),star(\{slots},\{rest}),(h : \{heap}))",
          seq([
            @tactics.undisch_tac(tm(pre)),
            arw(
              [
                thm("tlsf_small_page_heap"),
                thm("tlsf_small_used"),
                @lists.length(),
                @arith.add_clauses(),
              ] +
              ac,
            ),
          ]),
        ),
        free_have(
          "star(\{links},star(\{slots},\{rest}),(h : \{heap}))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("star_mono"), [
                "tlsf_small_links((loc : " + lw + "))",
                links,
                "star(" + slots + "," + rest + ")",
                "star(" + slots + "," + rest + ")",
                "(h : " + heap + ")",
              ]),
            ),
            arw([]),
            g => {
              let order = block_under(
                inst(
                  thm("tlsf_small_reclaim_list"),
                  args[:5].to_owned() +
                  ["(b : " + w + ") => tlsf_bytes(val(b)+8,4)"],
                ),
                g,
              )
              @tactics.accept_tac(
                @simp.rewrite_rule(ths([order]))(
                  inst(thm("tlsf_small_links_bytes"), ["(loc : " + lw + ")"]),
                ),
              )(g)
            },
          ]),
        ),
        free_have(
          "star(\{both},\{rest},(h : \{heap}))",
          seq([
            @tactics.undisch_tac(
              tm(
                "star(" +
                links +
                ",star(" +
                slots +
                "," +
                rest +
                "),(h : " +
                heap +
                "))",
              ),
            ),
            rw([@equal.gsym(thm("star_assoc")), thm("tlsf_small_istar_pair")]),
          ]),
        ),
        free_have(
          "∀ h0 : \{heap}, \{both}(h0) → \{array}(h0)",
          seq([
            @tactics.match_mp_tac(
              inst(thm("tlsf_small_istar_mono"), [total, pair, bytes]),
            ),
            gen,
            @tactics.disch_tac,
            @tactics.mp_tac(
              inst(thm("tlsf_small_recover_slot"), [
                "(p : " + w + ")",
                "(s : Num)",
                "(i : Num)",
                "emp",
              ]),
            ),
            arw(ac),
          ]),
        ),
        free_have(
          "star(\{array},\{rest},(h : \{heap}))",
          seq([
            @tactics.match_mp_tac(
              inst(thm("star_mono"), [
                both,
                array,
                rest,
                rest,
                "(h : " + heap + ")",
              ]),
            ),
            arw([]),
          ]),
        ),
        free_have(
          "\{array} == tlsf_bytes(val((p : \{w}))+32,\{len})",
          seq([
            @tactics.trans_tac(@theorems.eq_trans())(
              tm(
                "tlsf_istar((i : Num) => tlsf_bytes(val((p : " +
                w +
                "))+32+(8+(s : Num))*i,8+s)," +
                total +
                ")",
              ),
            ),
            @tactics.thenl(
              @tactics.conj_tac,
              @list.List([
                seq([
                  @tactics.match_mp_tac(thm("tlsf_istar_cong")),
                  gen,
                  @tactics.disch_tac,
                  g => {
                    @tactics.strip_assume_tac(
                      block_under(
                        inst(
                          thm("tlsf_small_slot_bounds"),
                          args + ["(i : Num)"],
                        ),
                        g,
                      ),
                    )(g)
                  },
                  arw([]),
                ]),
                rw([thm("tlsf_small_bytes_array")]),
              ]),
            ),
          ]),
        ),
        g => {
          let pack = @equal.conv_rule(
            @calc_num.num_reduce_conv,
            @simp.rewrite_rule(
              ths([
                @arith.add_clauses(),
                arith("∀ a : Num, ∀ n : Num, ∀ k : Num, a+n+k == a+(n+k)"),
              ]),
            )(
              block_under(
                inst(thm("tlsf_small_words6"), [
                  "val((p : " + w + "))+8",
                  "(cap : Num)",
                ]),
                g,
              ),
            ),
          )
          let tail = @simp.rewrite_rule(
            ths([
              @kernel.assume_rule(
                tm("\{len}+((cap : Num)-24-\{len}) == cap-24"),
              ),
            ]),
          )(
            inst(thm("tlsf_bytes_split"), [
              "val((p : " + w + "))+32",
              len,
              "(cap : Num)-24-" + len,
            ]),
          )
          let source = "star(" + array + "," + rest + ",(h : " + heap + "))"
          seq([
            @tactics.undisch_tac(tm(source)),
            ent_tac(
              [pack, tail, arith("∀ a : Num, ∀ k : Num, a+8+k == a+(8+k)")],
              [
                "(word((s : Num)) : " + w + ")",
                "(word(" + total + ") : " + w + ")",
                "(word(0) : " + w + ")",
                "tlsf_small_head((loc : " + lw + "))",
                "(prev : " + w + ")",
                "(next : " + w + ")",
              ],
            ),
          ])(g)
        },
      ])
    },
  )
}
