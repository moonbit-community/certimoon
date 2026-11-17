// Store sequences on owned cells; arbitrary remaining bytes are framed.

///|
fn prove_tlsf_ensure_writes() -> Unit raise {
  let w = w32
  let vc = seq([
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.rewrite_tac(
      ths([
        thm("star_assoc"),
        thm("star_comm"),
        thm("star_left_comm"),
        @words.word_and_0(),
        @words.word_or_0(),
      ]),
    ),
    @tactics.conv_tac(@words.word_reduce_conv),
  ])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (ps : Array[String]) => {
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    "(gs : List[Value]) => (ms : Num) => \{out}"
  }
  let r = "word_add(word_add((m : \{w}),word(8)),tlsf_size((hdr : \{w})))"
  let slot = "tlsf_top_cell((d : \{w}))"
  let clear = "word_and((hdr : \{w}),word(4294967293))"
  let a = "[\{i("m")},\{i("e")}]"
  let b = "[\{i("m")},\{i(r)}]"
  let p = pred([
    cell(slot, "m"),
    cell("m", "hdr"),
    cell(r, "word(0)"),
    cell("word_add(\{r},word(4))", "word(0)"),
  ])
  let q = pred([
    cell(slot, r),
    cell("m", clear),
    cell(r, "word(2)"),
    cell("word_add(\{r},word(4))", "m"),
  ])
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ hdr : \{w}, ∀ e : \{w}, ∀ fp : \{rty}"
  let rws = [thm("tlsf_size"), thm("tlsf_top_cell"), thm("tlsf_base")]
  ignore(
    sym_prove(
      "tlsf_ensure_used_before_size_raw",
      "\{vars}, sl_triple(st(NIL,\{a},\{p}),tlsf_ensure_used_before_size(d,pop,push),st([\{i(r)}],\{b},\{q}))",
      [],
      () => [vc],
      rws~,
    ),
  )
  let page = "(word(DIV((lim2 : Num),65536)) : \{w})"
  let cap = "tlsf_capacity_at((lim2 : Num),\{r})"
  let q2 = pred([
    cell(slot, r),
    cell("m", clear),
    cell(r, "word_or(\{cap},word(2))"),
    cell("word_add(\{r},word(4))", "m"),
  ])
  ignore(
    sym_prove(
      "tlsf_ensure_used_after_size_raw",
      "\{vars}, ∀ lim2 : Num, MOD(lim2,65536) == 0 → sl_triple(st([\{i(r)},\{i(page)}],\{b},\{q}),tlsf_ensure_used_after_size(d,pop,push),st(NIL,\{b},\{q2}))",
      [],
      () => [vc],
      rws=rws +
        [
          thm("tlsf_capacity_at"),
          @bool.undisch(inst(thm("tlsf_memory_byte_word"), ["(lim2 : Num)"])),
        ],
    ),
  )
  let f0 = pred([cell("m", "hdr")])
  let f1 = pred([
    cell(
      "m",
      "word_or(tlsf_capacity_at((lim2 : Num),(m : " +
      w +
      ")),word_and((hdr : " +
      w +
      "),word(3)))",
    ),
  ])
  ignore(
    sym_prove(
      "tlsf_ensure_free_before_size_raw",
      "\{vars}, sl_triple(st(NIL,\{a},\{f0}),tlsf_ensure_free_before_size(d,pop,push),st([\{i("m")}],\{a},\{f0}))",
      [],
      () => [],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_ensure_free_after_size_raw",
      "\{vars}, ∀ lim2 : Num, MOD(lim2,65536) == 0 → sl_triple(st([\{i("m")},\{i(page)}],\{a},\{f0}),tlsf_ensure_free_after_size(d,pop,push),st(NIL,\{a},\{f1}))",
      [],
      () => [vc],
      rws=[
        thm("tlsf_capacity_at"),
        @bool.undisch(inst(thm("tlsf_memory_byte_word"), ["(lim2 : Num)"])),
      ],
    ),
  )
}
