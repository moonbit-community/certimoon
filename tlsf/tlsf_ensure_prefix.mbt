// The compiled read-only prefix, including the guarded top getter.

///|
fn prove_tlsf_ensure_prefix() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let slot = "word_add(word_and(word_add((d : \{w}),word(15)),word(4294967280)),word(1908))"
  let frame = "(fp : \{rty})((gs : List[Value]),(lim : Num))"
  def(
    "tlsf_ensure_ro",
    "tlsf_ensure_ro((d : \{w}),(m : \{w}),(hdr : \{w}),(lim : Num),(before : \{heap}),(fp : \{rty}),(gs : List[Value]),(ms : Num),(h : \{heap})) == (ms == lim && h == before && star(\{cell(slot,"m")},star(\{cell("m","hdr")},\{frame}),h))",
  )
  let args = [
    "(d : \{w})",
    "(m : \{w})",
    "(hdr : \{w})",
    "(lim : Num)",
    "(before : \{heap})",
    "(fp : \{rty})",
  ]
  let r = "tlsf_ensure_ro(\{args.join(",")})"
  let vars = "∀ d : \{w}, ∀ m : \{w}, ∀ hdr : \{w}, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  for
    (name, a, x, rest) in [
      ("top", slot, "(m : \{w})", "star(\{cell("m","hdr")},\{frame})"),
      (
        "header",
        "(m : \{w})",
        "(hdr : \{w})",
        "star(\{cell(slot,"m")},\{frame})",
      ),
    ] {
    let read = lemma(
      "tlsf_ensure_ro_" + name,
      "\{vars}, ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{r}(gs,ms,h) → has_i32(h,val((\{a} : \{w})),\{x})",
      () => ent_tac([thm("tlsf_ensure_ro"), thm("has_i32")], [rest]),
    )
    let i = (a : String) => "V_num(ConstInt32((\{a} : \{w})))"
    let _ = lemma(
      "st_ensure_load_" + name,
      "\{vars}, ∀ v : List[Value], ∀ lc : List[Value], sl_triple(st(APPEND(v,[\{i(a)}]),lc,\{r}),[Load(T_i32,NONE,2,0)],st(APPEND(v,[\{i(x)}]),lc,\{r}))",
      () => {
        seq([
          gen,
          @tactics.match_mp_tac(
            inst(thm("st_load_read"), [
              "(v : List[Value])", "(lc : List[Value])", r, a, x, "2", "0",
            ]),
          ),
          rw([@arith.add_clauses()]),
          @tactics.accept_tac(inst(read, args)),
        ])
      },
    )
  }
  let i = (a : String) => "V_num(ConstInt32((\{a} : \{w})))"
  let e = "tlsf_ensure_expected((s : \{w}))"
  let page = "word_jushr(\{slot},word(16))"
  let locals = "[\{i(slot)},\{i(e)}]"
  let middle = "st([\{i(page)}],\{locals},\{r})"
  let current = "(word(DIV((lim : Num),65536)) : \{w})"
  let p2 = "st([\{i(page)},\{i(current)}],\{locals},\{r})"
  let post = "st([\{i("word_and((hdr : " + w + "),word(1))")}],[\{i("m")},\{i(e)}],\{r})"
  let cond = "!word_ugt((d : \{w}),word(4294965088))"
  let getter = "!word_uge(\{page},\{current})"
  let rules = step_rules + ["st_ensure_load_top", "st_ensure_load_header"]
  let rws = [
    thm("tlsf_ensure_expected"),
    thm("tlsf_round_code"),
    thm("tlsf_align"),
    thm("tlsf_base"),
    thm("tlsf_top_cell"),
  ]
  let _ = sym_prove(
    "tlsf_ensure_prefix_before_size_raw",
    "\{vars}, ∀ s : \{w}, ∀ pop : Num, ∀ push : Num, \{cond} → sl_triple(st(NIL,[\{i("s")},\{i("word(0)")}],\{r}),tlsf_ensure_prefix_before_size(d,pop,push),\{middle})",
    [],
    () => [rw([thm("tlsf_align"), thm("tlsf_base")])],
    afters=["st(NIL,[\{i("d")},\{i(e)}],\{r})"],
    rules~,
    rws~,
  )
  let _ = sym_prove(
    "tlsf_ensure_prefix_after_size_raw",
    "\{vars}, ∀ s : \{w}, ∀ pop : Num, ∀ push : Num, \{getter} → sl_triple(\{p2},tlsf_ensure_prefix_after_size(d,pop,push),\{post})",
    [],
    () => [],
    afters=["st([\{i("m")}],\{locals},\{r})"],
    rules~,
    rws~,
  )
  let size = @simp.rewrite_rule(ths([@lists.append()]))(
    inst(thm("st_memory_size_at"), ["[\{i(page)}]", locals, "(lim : Num)", r]),
  )
  let _ = lemma(
    "tlsf_ensure_prefix_raw",
    "\{vars}, ∀ s : \{w}, ∀ pop : Num, ∀ push : Num, \{cond} && \{getter} → sl_triple(st(NIL,[\{i("s")},\{i("word(0)")}],\{r}),tlsf_ensure_prefix(d,pop,push),\{post})",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_ensure_prefix_parts")]),
        @tactics.match_mp_tac(thm("sl_seq")),
        @tactics.exists_tac(tm(middle)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.match_mp_tac(thm("tlsf_ensure_prefix_before_size_raw")),
              arw([]),
            ]),
            seq([
              @tactics.subst1_tac(
                @equal.gsym(
                  @simp.rewrite_conv(ths([@lists.append()]))(
                    tm(
                      "APPEND([Memory_size],tlsf_ensure_prefix_after_size((d : \{w}),(pop : Num),(push : Num)))",
                    ),
                  ),
                ),
              ),
              @tactics.match_mp_tac(thm("sl_seq")),
              @tactics.exists_tac(tm(p2)),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @tactics.match_mp_tac(size),
                    gen,
                    rw([thm("tlsf_ensure_ro")]),
                    @meson.meson_tac(ths([])),
                  ]),
                  seq([
                    @tactics.match_mp_tac(
                      thm("tlsf_ensure_prefix_after_size_raw"),
                    ),
                    arw([]),
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
