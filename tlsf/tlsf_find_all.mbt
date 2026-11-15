// The compiled search against the combined allocator invariant.
// Preserve the exact saved heap, including allocator bytes with existential contents.

///|
fn prove_tlsf_find_all() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let large = "tlsf_large((d : \{w}), (limit : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let region = "tlsf_chain((d : \{w}), (limit : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}))"
  let inv = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (limit : Num) && h == (before : \{heap}) && star(\{large}, (fp : \{rty})(gs, ms), h)"
  let frames = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (limit : Num) && tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt})) && star(\{region}, (fp : \{rty})(gs, ms), h)"
  let ro = "tlsf_ro((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (before : \{heap}), (\{frames}))"
  let search = "tlsf_search((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let value = (x : String) => "V_num(ConstInt32(\{x}))"
  let locals = "[\{value("(s : \{w})")}, \{value("word(0)")}, \{value("word(0)")}, \{value("word(0)")}, \{value("word(0)")}, \{value("word(0)")}]"
  let path = inst(thm("tlsf_find_query"), [
    "(s : \{w})",
    "(d : \{w})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(before : \{heap})",
    frames,
  ])
  let concl = @basics.dest_imp(@kernel.concl(path)).1
  let parts = args_of(concl, "sl_triple", 3).unwrap()
  let pure_pre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => tlsf_search_domain((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w})) && (\{show(parts[0])})(vs, lc, gs, ms, h)"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let eqs = [thm("st"), thm("tlsf_large"), thm("tlsf_ro")] + lift_rws() + ac
  let pre = seq([
    gen,
    rw(eqs),
    strip,
    have(
      "\{ro}((gs : List[Value]), (ms : Num), (h : \{heap}))",
      seq([
        rw(eqs),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(eqs),
      ]),
    ),
    have(
      "tlsf_search_domain((s : \{w}), (fl : \{w}), (sb : (Num) -> \{w}))",
      seq([
        @tactics.match_mp_tac(
          inst(thm("tlsf_ro_domain"), [
            "(s : \{w})",
            "(d : \{w})",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(before : \{heap})",
            frames,
            "(gs : List[Value])",
            "(ms : Num)",
            "(h : \{heap})",
          ]),
        ),
        arw([]),
      ]),
    ),
    arw(eqs),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw(eqs),
  ])
  let post = seq([
    gen,
    rw(eqs),
    strip,
    have(
      "star(\{large}, (fp : \{rty})((gs : List[Value]), (ms : Num)), (h : \{heap}))",
      seq([
        rw(eqs),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(eqs),
      ]),
    ),
    have(
      "tlsf_find_result((s : \{w}), (xs : \{lw}), (hd : \{ht}), \{search})",
      seq([
        @tactics.match_mp_tac(
          inst(thm("tlsf_large_search_sound_frame"), [
            "(s : \{w})",
            "(d : \{w})",
            "(limit : Num)",
            "(top : \{w})",
            "(xs : \{lw})",
            "(hd : \{ht})",
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(fp : \{rty})((gs : List[Value]), (ms : Num))",
            "(h : \{heap})",
          ]),
        ),
        arw([]),
      ]),
    ),
    arw(eqs),
    @tactics.exists_tac(tm(search)),
    arw(eqs),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw(eqs),
  ])
  let result = @tactics.prove(
    tm(
      "∀ s : \{w}, ∀ d : \{w}, ∀ limit : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ before : \{heap}, ∀ fp : \{rty}, 16 <= val(s) && val(s) <= 4160749568 → sl_triple(st(NIL, \{locals}, \{inv}), tlsf_find_code(d), (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(3, lc) == \{value("tlsf_align(s)")} && (\{inv})(gs, ms, h) && (∃ m : \{w}, vs == [\{value("m")}] && m == \{search} && tlsf_find_result(s, xs, hd, m)))",
    ),
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_conseq")),
      @tactics.exists_tac(tm(pure_pre)),
      @tactics.exists_tac(parts[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          pre,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              seq([
                @tactics.match_mp_tac(thm("sl_pure")),
                @tactics.disch_tac,
                rw([@class.eta_ax()]),
                @tactics.match_mp_tac(path),
                arw([]),
              ]),
              post,
            ]),
          ),
        ]),
      ),
    ]),
  )
  record("tlsf_find_all", result, kind="example")
}
