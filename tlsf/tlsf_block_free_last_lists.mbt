// A last release removes the page from both the page set and its class's
// partial list. Its cached list is empty, so no fast-list owner is lost.

///|
fn prove_tlsf_block_free_last_lists() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let v = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}, ∀ b : \{w}"
  let args = "(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw})"
  let part = "(j : Num) => tlsf_small_remove((p : \{w}),(partial : (Num) -> \{lw})(j))"
  let narg = "tlsf_small_remove((p : \{w}),ps),sz,tlsf_block_free_loc(loc,p,(b : \{w})),cached,tlsf_block_free_live(live,p,b),fast,(\{part})"
  let _ = lemma(
    "tlsf_small_lists_remove_empty_page",
    "\{v}, tlsf_small_lists_ok(\{args}) && (cached : \{ls})(p) == NIL → tlsf_small_lists_ok(\{narg})",
    seq([
      gen,
      strip,
      @tactics.undisch_tac(tm("tlsf_small_lists_ok(" + args + ")")),
      rw([thm("tlsf_small_lists_ok")]),
      strip,
      rw([
        thm("tlsf_small_lists_ok"),
        thm("tlsf_small_remove_member"),
        thm("tlsf_block_free_live"),
        thm("tlsf_block_free_loc"),
        thm("tlsf_small_put"),
      ]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.x_gen_tac(tm("(q : " + w + ")")),
              strip,
              arw([thm("tlsf_small_remove_count")]),
              small_meson(ths([])),
            ]),
          ),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(j : Num)")),
              @tactics.x_gen_tac(tm("(a : " + w + ")")),
              strip,
              free_have(
                "∃ owner : \{w}, MEM(owner,(ps : \{lw})) && (sz : (\{w}) -> Num)(owner) == 8*(j : Num) && MEM((a : \{w}),(cached : \{ls})(owner))",
                small_meson(ths([])),
              ),
              @tactics.first_x_assum(th => {
                if @basics.is_exists(@kernel.concl(th)) {
                  @tactics.x_choose_then(tm("(owner : " + w + ")"))(th => {
                    @tactics.strip_assume_tac(th)
                  })(th)
                } else {
                  @tactics.no_tac
                }
              }),
              free_have(
                "!((owner : \{w}) == (p : \{w}))",
                small_meson(ths([@lists.mem()])),
              ),
              @tactics.exists_tac(tm("(owner : " + w + ")")),
              arw([]),
            ]),
          ),
          solve(
            seq([
              @tactics.x_gen_tac(tm("(j : Num)")),
              @tactics.x_gen_tac(tm("(q : " + w + ")")),
              strip,
              arw([]),
              small_meson(ths([])),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let cls = "DIV((sz : (\{w}) -> Num)((p : \{w})),8)"
  let single = "tlsf_small_put_class((partial : (Num) -> \{lw}),\{cls},tlsf_small_remove((p : \{w}),partial(\{cls})))"
  let _ = lemma(
    "tlsf_small_partial_remove_class",
    "\{v}, tlsf_small_lists_ok(\{args}) && 8 <= sz(p) && sz(p) <= 256 && MOD(sz(p),8) == 0 → (∀ j : Num, j < 33 → (\{single})(j) == tlsf_small_remove(p,partial(j)))",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_small_class_bounds"), [
          "(sz : (" + w + ") -> Num)((p : " + w + "))",
        ]),
      ),
      arw([]),
      strip,
      @tactics.undisch_tac(tm("tlsf_small_lists_ok(" + args + ")")),
      rw([thm("tlsf_small_lists_ok")]),
      strip,
      @tactics.x_gen_tac(tm("(j : Num)")),
      @tactics.disch_tac,
      rw([thm("tlsf_small_put_class")]),
      @class.cond_cases_tac,
      arw([]),
      free_have(
        "!MEM((p : \{w}),(partial : (Num) -> \{lw})((j : Num)))",
        seq([
          @class.refute_then(th => @tactics.assume_tac(th)),
          free_have(
            "(sz : (\{w}) -> Num)((p : \{w})) == 8*(j : Num)",
            small_meson(ths([])),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      @tactics.conv_tac(@equal.sym_conv),
      @tactics.match_mp_tac(thm("tlsf_small_remove_absent")),
      arw([]),
    ]),
  )
}
