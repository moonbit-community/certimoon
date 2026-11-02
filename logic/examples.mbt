// Programs verified with the rules alone: each step is a rule instance,
// glued with sl_seq, and sl_conseq where one rule's postcondition is not
// literally the next rule's precondition.

///|
/// `th` with its beta-redexes reduced.
fn beta(th : @kernel.Thm) -> @kernel.Thm raise {
  @simp.rewrite_rule(ths([]))(th)
}

///|
/// (p, bs, q) of `sl_triple(p, bs, q)`.
fn triple_parts(th : @kernel.Thm) -> (@kernel.Term, @kernel.Term, @kernel.Term) raise {
  let (_, args) = @basics.strip_comb(@kernel.concl(th))
  guard args.to_array() is [p, bs, q] else {
    raise Failure("wasmcert/logic: not a triple: " + show(@kernel.concl(th)))
  }
  (p, bs, q)
}

///|
/// ⊢ ∀ vs ls h. a(vs, ls, h) → b(vs, ls, h): the stacks agree after
/// reassociating appends, and the rest follows from the premise.
fn entails(a : @kernel.Term, b : @kernel.Term) -> @kernel.Thm raise {
  let vs = tm("(vs : List[Value])")
  let ls = tm("(ls : List[Value])")
  let h = tm("(h : \{heap})")
  let app = (t : @kernel.Term) => @basics.list_mk_comb(t, @list.List([vs, ls, h]))
  let goal = @bool.list_mk_forall(@list.List([vs, ls, h]), @bool.mk_imp(app(a), app(b)))
  @tactics.prove(
    goal,
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([@equal.gsym(@lists.append_assoc()), @lists.append()])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
}

///|
/// t1 then t2: sl_seq, after weakening t2's precondition to t1's
/// postcondition when they differ.
fn then_rule(t1 : @kernel.Thm, t2 : @kernel.Thm) -> @kernel.Thm raise {
  let t1 = beta(t1)
  let t2 = beta(t2)
  let (_, _, q1) = triple_parts(t1)
  let (p2, _, q2) = triple_parts(t2)
  let t2 = if @basics.aconv(q1, p2) {
    t2
  } else {
    @drule.match_mp(thm("sl_conseq"))(
      @bool.conj(entails(q1, p2), @bool.conj(t2, entails(q2, q2))),
    )
  }
  @simp.rewrite_rule(ths([@lists.append()]))(
    @drule.match_mp(thm("sl_seq"))(@bool.conj(t1, t2)),
  )
}

///|
/// deserialise_i32 undoes serialise_i32: loading back what was stored
/// gives the value.
fn prove_roundtrip() -> @kernel.Thm raise {
  let num_of_le = lemma(
    "num_of_le_bytes",
    "∀ k : Num, ∀ n : Num, num_of_bytes(le_bytes(k, n)) == MOD(n, EXP(256, k))",
    seq([
      @nums.induct_tac,
      @simp.rewrite_tac(
        ths([
          @wasm.thm("le_bytes"),
          @wasm.thm("num_of_bytes"),
          @arith.exp(),
          @arith.mod_1(),
          @words.val_word(),
          @words.dimindex_8(),
          @arith.mod_mult_mod(),
        ]),
      ),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.try_tac(@simp.rewrite_tac(ths([@arith.add_sym()]))),
    ]),
  )
  let bound = @equal.conv_rule(
    @calc_num.num_reduce_conv,
    @simp.rewrite_rule(ths([@words.dimindex_32()]))(
      @bool.ispec(tm("(v : \{w32})"), @words.val_bound()),
    ),
  )
  lemma(
    "deserialise_serialise_i32",
    "∀ v : \{w32}, deserialise_i32(serialise_i32(v)) == v",
    seq([
      @tactics.gen_tac,
      @simp.rewrite_tac(ths([@wasm.thm("deserialise_i32"), @wasm.thm("serialise_i32"), num_of_le])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.simp_tac(ths([@arith.mod_lt(), bound, @words.word_val()])),
    ]),
  )
}

///|
fn prove_examples() -> Unit raise {
  let roundtrip = prove_roundtrip()
  // [i32.const k; i32.const v; i32.store; i32.const k; i32.load]: it loads
  // back v from val(k) + off, and the frame p still holds
  let addr = "val((k : \{w32})) + (off : Num)"
  let p = "(p : \{sassn})"
  let bs = "(bs : List[\{w8}])"
  let k = tm("ConstInt32((k : \{w32}))")
  let v = tm("ConstInt32((v : \{w32}))")
  let length = tm("LENGTH(\{bs}) == 4")
  let pre = tm(
    "(vs : List[Value]) => (ls : List[Value]) => (h : \{heap}) => star(pts(\{addr}, \{bs}), \{p}(vs, ls), h)",
  )
  let const_rule = (q : @kernel.Term, c : @kernel.Term) => beta(
    @bool.ispecl(@list.List([q, c]), thm("sl_const")),
  )
  let t1 = const_rule(pre, k)
  let t2 = const_rule(triple_parts(t1).2, v)
  let vars = (xs : Array[String]) => @list.List(xs.map(tm))
  let t3 = @bool.mp(
    @bool.ispecl(
      vars([p, "(k : \{w32})", "(a : Num)", "(off : Num)", "(v : \{w32})", bs]),
      thm("sl_store_i32"),
    ),
    @kernel.assume_rule(length),
  )
  let t4 = const_rule(triple_parts(beta(t3)).2, k)
  let t5 = @bool.mp(
    @bool.ispecl(
      vars([p, "(k : \{w32})", "(a : Num)", "(off : Num)", "serialise_i32((v : \{w32}))"]),
      thm("sl_load_i32"),
    ),
    @bool.spec(tm("(v : \{w32})"), thm("serialise_i32_length")),
  )
  let th = then_rule(then_rule(then_rule(then_rule(t1, t2), t3), t4), t5)
  let th = @simp.rewrite_rule(ths([roundtrip]))(th)
  record("example_store_load", @bool.gen_all(@bool.disch(length, th)), kind="example")
}
