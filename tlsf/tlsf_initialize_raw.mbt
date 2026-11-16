// The metadata stores operate only on their owned words. All remaining
// startup bytes and client assertions pass through these triples as frames.

///|
fn prove_tlsf_initialize_raw() -> Unit raise {
  let w = w32
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let base = "tlsf_base((d : \{w}))"
  let m = "tlsf_initialize_origin((d : \{w}))"
  let lc = "[\{i(m)},(l1 : Value),(l2 : Value)]"
  let oldlc = "[\{i(base)},(l1 : Value),(l2 : Value)]"
  let pred = (a : String, v : String) => {
    "(gs : List[Value]) => (ms : Num) => star(\{cell(a,v)},(fp : \{rty})(gs,ms))"
  }
  let vc = seq([
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    rw([
      thm("star_assoc"),
      thm("star_comm"),
      thm("star_left_comm"),
      @words.word_and_0(),
      @words.word_or_0(),
    ]),
    @tactics.conv_tac(@words.word_reduce_conv),
  ])
  let vars = "∀ d : \{w}, ∀ push : Num, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  ignore(
    sym_prove(
      "tlsf_initialize_arithmetic_raw",
      "\{vars}, ∀ l0 : Value, sl_triple(st(NIL,[(l0 : Value),l1,l2],fp),tlsf_initialize_arithmetic(d,push),st(NIL,[\{i(base)},\{i("tlsf_initialize_required((d : " + w + "))")},l2],fp))",
      [],
      [],
      rws=[thm("tlsf_base"), thm("tlsf_initialize_required")],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_initialize_mark_raw",
      "\{vars}, sl_triple(st(NIL,\{oldlc},\{pred(m,"word(0)")}),tlsf_initialize_mark(d,push),st(NIL,\{lc},\{pred(m,"word(2)")}))",
      [],
      [vc],
      rws=[thm("tlsf_initialize_origin"), thm("tlsf_base")],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_initialize_size_before_raw",
      "\{vars}, ∀ R : \{rty}, sl_triple(st(NIL,\{lc},R),tlsf_initialize_size_before(d,push),st([\{i(m)}],\{lc},R))",
      [],
      [],
    ),
  )
  let page = "(word(DIV((lim : Num),65536)) : \{w})"
  let hdr = "tlsf_initialize_header((d : \{w}),(lim : Num))"
  ignore(
    sym_prove(
      "tlsf_initialize_size_after_raw",
      "\{vars}, ∀ lim : Num, MOD(lim,65536) == 0 → sl_triple(st([\{i(m)},\{i(page)}],\{lc},\{pred(m,"word(2)")}),tlsf_initialize_size_after(d,push),st(NIL,\{lc},\{pred(m,hdr)}))",
      [],
      [vc],
      rws=[
        thm("tlsf_initialize_header"),
        thm("tlsf_capacity_at"),
        @bool.undisch(inst(thm("tlsf_memory_byte_word"), ["(lim : Num)"])),
      ],
    ),
  )
  let slot = "tlsf_top_cell((d : \{w}))"
  ignore(
    sym_prove(
      "tlsf_initialize_top_raw",
      "\{vars}, sl_triple(st(NIL,\{lc},\{pred(slot,"word(0)")}),tlsf_initialize_top(d,push),st(NIL,\{lc},\{pred(slot,m)}))",
      [],
      [vc],
      rws=[thm("tlsf_top_cell"), thm("tlsf_base")],
    ),
  )
  let _ = lemma(
    "tlsf_initialize_size_parts",
    "∀ d : \{w}, ∀ push : Num, tlsf_initialize_size(d,push) == APPEND(tlsf_initialize_size_before(d,push),APPEND([Memory_size],tlsf_initialize_size_after(d,push)))",
    rw([
      thm("tlsf_initialize_size"),
      thm("tlsf_initialize_size_before"),
      thm("tlsf_initialize_size_after"),
      @lists.append(),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_tail_parts",
    "∀ d : \{w}, ∀ push : Num, tlsf_initialize_tail(d,push) == APPEND(tlsf_initialize_mark(d,push),APPEND(tlsf_initialize_size(d,push),APPEND(tlsf_initialize_publish(d,push),tlsf_initialize_top(d,push))))",
    rw([
      thm("tlsf_initialize_tail"),
      thm("tlsf_initialize_mark"),
      thm("tlsf_initialize_size"),
      thm("tlsf_initialize_publish"),
      thm("tlsf_initialize_top"),
      @lists.append(),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_parts",
    "∀ d : \{w}, ∀ push : Num, tlsf_initialize_code(d,push) == APPEND(tlsf_initialize_arithmetic(d,push),APPEND(tlsf_initialize_check(d,push),APPEND(tlsf_initialize_grow(d,push),tlsf_initialize_tail(d,push))))",
    rw([
      thm("tlsf_initialize_code"),
      thm("tlsf_initialize_arithmetic"),
      thm("tlsf_initialize_check"),
      thm("tlsf_initialize_grow"),
      thm("tlsf_initialize_tail"),
      @lists.append(),
    ]),
  )
}
