// A persistent read view of a heap. Unlike owning a cell, this view can
// accompany an arbitrary assertion about the entire heap, including its
// equality to a saved heap. Loads preserve that assertion exactly.

///|
fn prove_readonly_load() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  def(
    "has_i32",
    "has_i32((h : \{heap}), (a : Num), (x : \{w})) == (∃ q : \{hprop}, star(pts(a, serialise_i32(x)), q, h))",
  )
  let has = thm("has_i32")
  let _ = lemma(
    "has_i32_star",
    "∀ p : \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, ∀ a : Num, ∀ x : \{w}, star((h0 : \{heap}) => p(h0) && has_i32(h0, a, x), r, h) → has_i32(h, a, x)",
    seq([
      gen,
      rw([thm("star")]),
      strip,
      @tactics.undisch_tac(tm("has_i32((h1 : \{heap}), (a : Num), (x : \{w}))")),
      rw([has]),
      strip,
      @tactics.exists_tac(tm("star((q : \{hprop}), (r : \{hprop}))")),
      rw([@equal.gsym(thm("star_assoc"))]),
      @simp.once_rewrite_tac(ths([thm("star")])),
      beta_goal(),
      @tactics.exists_tac(tm("(h1 : \{heap})")),
      @tactics.exists_tac(tm("(h2 : \{heap})")),
      arw([]),
    ]),
  )
  let _ = lemma(
    "has_i32_load",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ off : Num, ∀ x : \{w}, has_i32(heap_of(m), n + off, x) → load(m, n, off, 4) == SOME(serialise_i32(x))",
    seq([
      gen,
      rw([has]),
      strip,
      @tactics.mp_tac(
        readonly_inst(thm("load_pts"), [
          "(m : \{mem_ty})",
          "(n : Num)",
          "(off : Num)",
          "serialise_i32((x : \{w}))",
          "(q : \{hprop})",
        ]),
      ),
      arw([
        thm("serialise_i32_length"),
        @equal.gsym(@lists.length_eq_nil()),
        arith("!(4 == 0)"),
      ]),
    ]),
  )
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let k = "Basic(EConstNum(ConstInt32((k : \{w}))))"
  let load = "Basic(Load(T_i32, NONE, (a : Num), (off : Num)))"
  let prefix = @bool.gen_all(thm("prefix_load"))
  let cases = @wasm.step_cases(s, f, tm("[\{k}, \{load}]"))
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let mem = "EL((j : Num), s_mems((s : Wstore)))"
  let ph = "(h0 : \{heap}) => (p : \{sassn})((vs0 : List[Value]), f_locs((f : Wframe)), gvals((s : Wstore), f), mem_length(\{mem}), h0)"
  let _ = prove_value_rule(
    "sl_load_read",
    "∀ p : \{sassn}, ∀ k : \{w}, ∀ x : \{w}, ∀ a : Num, ∀ off : Num, sl_triple((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(k))]) && p(vs0, lc, gs, ms, h) && has_i32(h, val(k) + off, x), [Load(T_i32, NONE, a, off)], (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(x))]) && p(vs0, lc, gs, ms, h) && has_i32(h, val(k) + off, x))",
    [k],
    load,
    "wasm_deserialise_num(serialise_i32((x : \{w})), T_i32)",
    prefix,
    cases,
    seq([
      @tactics.match_mp_tac(rb[12]),
      @tactics.exists_tac(tm("(j : Num)")),
      @tactics.exists_tac(tm(mem)),
      arw([@wasm.thm("t_num_length")]),
    ]),
    facts=have(
      "load(\{mem}, val((k : \{w})), (off : Num), 4) == SOME(serialise_i32((x : \{w})))",
      seq([
        @tactics.match_mp_tac(
          readonly_inst(thm("has_i32_load"), [
            mem,
            "val((k : \{w}))",
            "(off : Num)",
            "(x : \{w})",
          ]),
        ),
        @tactics.match_mp_tac(
          readonly_inst(thm("has_i32_star"), [
            ph,
            "(r : \{hprop})",
            "heap_of(\{mem})",
            "val((k : \{w})) + (off : Num)",
            "(x : \{w})",
          ]),
        ),
        arw([]),
      ]),
    ),
    unfold=[
        "smem_ind", "load", "read_bytes", "mem_length", "deserialise_i32", "t_num_length",
        "wasm_deserialise_num",
      ].map(@wasm.thm) +
      [
        thm("deserialise_serialise_i32"),
        @simp.rewrite_rule(ths([@wasm.thm("deserialise_i32")]))(
          thm("deserialise_serialise_i32"),
        ),
      ],
  )
  let v = "(v : List[Value])"
  let l = "(l : List[Value])"
  let rr = "(R : \{rty})"
  let source = readonly_inst(thm("sl_load_read"), [
    "st(\{v}, \{l}, \{rr})",
    "(k : \{w})",
    "(x : \{w})",
    "(a : Num)",
    "(off : Num)",
  ])
  let triple = args_of(@kernel.concl(source), "sl_triple", 3).unwrap()
  let ent = seq([
    gen,
    rw([thm("st")]),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @tactics.try_tac(@tactics.exists_tac(tm(v))),
    arw([]),
    @tactics.try_tac(@meson.asm_meson_tac(ths([]))),
  ])
  let _ = lemma(
    "st_load_read",
    "∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ k : \{w}, ∀ x : \{w}, ∀ a : Num, ∀ off : Num, (∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, R(gs, ms, h) → has_i32(h, val(k) + off, x)) → sl_triple(st(APPEND(v, [V_num(ConstInt32(k))]), l, R), [Load(T_i32, NONE, a, off)], st(APPEND(v, [V_num(ConstInt32(x))]), l, R))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_conseq")),
      @tactics.exists_tac(triple[0]),
      @tactics.exists_tac(triple[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          ent,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([@tactics.accept_tac(source), ent]),
          ),
        ]),
      ),
    ]),
  )
}

///|
fn readonly_inst(th : @kernel.Thm, xs : Array[String]) -> @kernel.Thm raise {
  @bool.ispecl(@list.List(xs.map(tm)), th)
}
