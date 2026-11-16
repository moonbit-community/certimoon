// Once a trap is at the top, reduction can only discard context. In
// particular it cannot execute a later store, call, or memory.grow.

///|
fn prove_abort_traps() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let top = @wasm.thm("trap_top")
  let vals = [
    @wasm.thm("is_val_clauses"),
    @wasm.thm("is_val_basic"),
    @wasm.thm("all_vals_map"),
    @lists.all(),
    @lists.all_append(),
  ]
  let _ = lemma(
    "abort_trap_nonvalues",
    "∀ es : List[Einstr], trap_top(es) → !ALL(is_val,es)",
    seq([
      rw([top]),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths(vals))),
      arw([]),
    ]),
  )
  let _ = lemma(
    "abort_trap_first_nonvalue",
    "∀ vs : List[Value], ∀ x : Einstr, ∀ rest : List[Einstr], !is_val(x) → (trap_top(APPEND(MAP(v_to_e,vs),CONS(x,rest))) == (x == Trap))",
    seq([
      gen,
      @tactics.disch_tac,
      rw([top]),
      @tactics.eq_tac,
      @tactics.first(
        @list.List([
          solve(
            seq([
              strip,
              @meson.asm_meson_tac(ths([thm("first_nonval_eq")] + vals)),
            ]),
          ),
          solve(
            seq([
              @tactics.disch_tac,
              subst_vars(),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(tm("(rest : List[Einstr])")),
              rw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let nottrap = @simp.rewrite_rule(ths([@lists.map(), @lists.cons_11()]))(
    @bool.spec(tm("[(v : Value)]"), thm("vals_not_trap")),
  )
  let head = @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
    @bool.spec(tm("(NIL : List[Value])"), thm("abort_trap_first_nonvalue")),
  )
  let ctor = @ind_types.distinctness("einstr")
  let _ = lemma(
    "abort_trap_drop_values",
    "∀ vs : List[Value], ∀ es : List[Einstr], trap_top(APPEND(MAP(v_to_e,vs),es)) == trap_top(es)",
    seq([
      @lists.list_induct_tac,
      rw([@lists.map(), @lists.append()]),
      gen,
      rw([
        top,
        @wasm.thm("cons_eq_append"),
        @wasm.thm("map_v_to_e_eq_cons"),
        thm("v_to_e_inj"),
        nottrap,
        @bool.gen_all(nottrap),
        @equal.gsym(@bool.gen_all(nottrap)),
        @lists.map_eq_nil(),
        @lists.cons_11(),
      ]),
      rw([@theorems.left_exists_and_thm(), @theorems.right_exists_and_thm()]),
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
      arw([@equal.gsym(top)]),
      @meson.asm_meson_tac(ths([top])),
    ]),
  )
  let _ = lemma(
    "abort_trap_append",
    "∀ es : List[Einstr], ∀ rest : List[Einstr], !ALL(is_val,es) → (trap_top(APPEND(es,rest)) == trap_top(es))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.eq_tac,
      @tactics.first(
        @list.List([
          solve(@meson.asm_meson_tac(ths([@wasm.thm("trap_top_prefix")]))),
          solve(
            seq([
              rw([top]),
              strip,
              subst_vars(),
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @tactics.exists_tac(
                tm("APPEND((r : List[Einstr]),(rest : List[Einstr]))"),
              ),
              rw([@equal.gsym(@lists.append_assoc()), @lists.append()]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "abort_trap_context",
    "∀ lh : Lholed, ∀ es : List[Einstr], !ALL(is_val,es) → (trap_top(lfill(lh,es)) == (lh_depth(lh) == 0 && trap_top(es)))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.struct_cases_tac(
        @bool.spec(tm("(lh : Lholed)"), @ind_types.cases("lholed")),
      ),
      rw([
        @wasm.thm("lfill"),
        @wasm.thm("lh_depth"),
        thm("abort_trap_drop_values"),
      ]),
      @tactics.first(
        @list.List([
          solve(@simp.asm_simp_tac(ths([thm("abort_trap_append")]))),
          solve(
            seq([
              @simp.simp_tac(
                ths([thm("abort_trap_first_nonvalue"), head, ctor] + vals),
              ),
              @int.arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
  let skip = @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
    @bool.spec(tm("[(v : Value)]"), thm("abort_trap_drop_values")),
  )
  let skip_num = @bool.gen_all(
    @simp.rewrite_rule(
      ths([@lists.map(), @lists.append(), @wasm.thm("v_to_e")]),
    )(@bool.spec(tm("[V_num((v : V_num))]"), thm("abort_trap_drop_values"))),
  )
  let skip_vec = @bool.gen_all(
    @simp.rewrite_rule(
      ths([@lists.map(), @lists.append(), @wasm.thm("v_to_e")]),
    )(@bool.spec(tm("[V_vec((v : V_vec))]"), thm("abort_trap_drop_values"))),
  )
  let skip_ref = @bool.gen_all(
    @simp.rewrite_rule(
      ths([@lists.map(), @lists.append(), @wasm.thm("v_to_e")]),
    )(@bool.spec(tm("[V_ref((v : V_ref))]"), thm("abort_trap_drop_values"))),
  )
  let literal = @tactics.prove(
    tm("trap_top([Trap])"),
    seq([
      rw([top]),
      @tactics.exists_tac(tm("(NIL : List[Value])")),
      @tactics.exists_tac(tm("(NIL : List[Einstr])")),
      rw([@lists.map(), @lists.append()]),
    ]),
  )
  let facts = [
      @ind_types.distinctness("b_e"),
      @equal.gsym(@ind_types.distinctness("b_e")),
      @bool.gen_all(skip),
      skip_num,
      skip_vec,
      skip_ref,
      literal,
      head,
      ctor,
    ] +
    vals
  let _ = lemma(
    "abort_trap_simple",
    "∀ es : List[Einstr], ∀ es2 : List[Einstr], reduce_simple(es,es2) → (trap_top(es) → trap_top(es2))",
    seq([
      @tactics.match_mp_tac(@wasm.thm("reduce_simple_induct")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(
        @simp.simp_rule(
          ths(
            [
              thm("abort_trap_first_nonvalue"),
              head,
              ctor,
              thm("abort_trap_drop_values"),
              @lists.append(),
              @lists.map(),
            ] +
            facts,
          ),
        ),
      ),
      arw(facts),
      @tactics.try_tac(
        @meson.asm_meson_tac(ths([@wasm.thm("lfilled_trap_iff")])),
      ),
    ]),
  )
  let _ = lemma(
    "abort_trap_reduce_strong",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → !ALL(is_val,es) && (trap_top(es) → s2 == s && f2 == f && trap_top(es2))",
    seq([
      @tactics.match_mp_tac(@wasm.thm("reduce_induct")),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.rule_assum_tac(
        @simp.rewrite_rule(ths([@wasm.thm("lfilled_eq")])),
      ),
      subst_vars(),
      @tactics.rule_assum_tac(
        @simp.simp_rule(
          ths(
            [
              thm("abort_trap_first_nonvalue"),
              head,
              ctor,
              thm("abort_trap_drop_values"),
              @lists.append(),
              @lists.map(),
            ] +
            facts,
          ),
        ),
      ),
      @simp.asm_simp_tac(ths(facts)),
      @tactics.try_tac(
        @meson.asm_meson_tac(
          ths([
            @wasm.thm("lfill_vals"),
            @wasm.thm("reduce_simple_ok"),
            thm("abort_trap_simple"),
            thm("abort_trap_context"),
            thm("abort_trap_nonvalues"),
            @wasm.thm("lfilled_eq"),
            @wasm.thm("reduce_ok"),
          ]),
        ),
      ),
    ]),
  )
  let _ = lemma(
    "abort_trap_reduce",
    "∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s,f,es,s2,f2,es2) → (trap_top(es) → s2 == s && f2 == f && trap_top(es2))",
    @meson.meson_tac(ths([thm("abort_trap_reduce_strong")])),
  )
  let _ = lemma(
    "safe_abort_top_trap",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ a : (Wstore,Wframe) -> Bool, trap_top(es) && a(s,f) → safe_abort(n,s,f,es,q,a)",
    seq([
      @nums.induct_tac,
      rw([thm("safe_abort")]),
      gen,
      strip,
      @class.asm_cases_tac(tm("(es : List[Einstr]) == [Trap]")),
      arw([]),
      @tactics.disj2_tac,
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.exists_tac(tm("(s : Wstore)")),
              @tactics.exists_tac(tm("(f : Wframe)")),
              @tactics.exists_tac(tm("([Trap] : List[Einstr])")),
              @tactics.match_mp_tac(thm("trap_step")),
              arw([]),
            ]),
          ),
          solve(
            seq([
              gen,
              @tactics.disch_then(th => {
                @tactics.mp_tac(@drule.match_mp(thm("abort_trap_reduce"))(th))
              }),
              arw([]),
              strip,
              subst_vars(),
              @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
