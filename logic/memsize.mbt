// Rules for memory.size and memory.grow.
//
// Assertions see the memory's length in bytes (ms, from lift). memory.size
// pushes it in pages, DIV(ms, 65536). memory.grow by c pages either fails
// (it may always fail: it pushes -1, and nothing changes) or appends
// c * 65536 zero bytes at the old end: it pushes the old size in pages, ms
// grows by c * 65536, and the zeros are a new points-to beside the
// precondition (star_grow), which the frame never sees.

///|
fn prove_memory_size_rules() -> Unit raise {
  let s = tm("(s : Wstore)")
  let f = tm("(f : Wframe)")
  let w = w32
  let m = "(m : \{mem_ty})"
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  let mem_defs = [@wasm.thm("mem_append"), @wasm.thm("mem_length"), @pair.snd()]
  let length_append = lemma(
    "mem_length_append",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ b : \{w8}, mem_length(mem_append(m, n, b)) == mem_length(m) + n",
    @simp.rewrite_tac(ths(mem_defs + [@lists.length_append(), @lists.length_replicate()])),
  )
  let heap_append = lemma(
    "heap_of_append",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ b : \{w8}, heap_of(mem_append(m, n, b)) == hunion(heap_of(m), pts_heap(mem_length(m), REPLICATE(n, b)))",
    seq([
      @simp.rewrite_tac(
        ths(
          mem_defs +
          [@class.fun_eq_thm(), thm("heap_of"), thm("hunion"), thm("pts_heap"), @lists.length_append(), @lists.length_replicate(), @lists.el_append()],
        ),
      ),
      @tactics.repeat_tac(@tactics.gen_tac),
      @class.asm_cases_tac(tm("(x : Num) < LENGTH(SND(\{m}))")),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.repeat_tac(@class.cond_cases_tac),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.try_tac(@int.asm_arith_tac),
    ]),
  )
  let heap_disj = lemma(
    "heap_of_disj",
    "∀ m : \{mem_ty}, ∀ zs : List[\{w8}], hdisj(heap_of(m), pts_heap(mem_length(m), zs))",
    seq([
      @simp.rewrite_tac(ths([thm("hdisj"), thm("pts_heap_none"), thm("heap_of"), @wasm.thm("mem_length")])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @class.cond_cases_tac,
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.try_tac(@int.asm_arith_tac),
    ]),
  )
  let star = thm("star")
  let star_intro = lemma(
    "star_intro",
    "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ h1 : \{heap}, ∀ h2 : \{heap}, hdisj(h1, h2) && p(h1) && q(h2) → star(p, q, hunion(h1, h2))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  let star_or = lemma(
    "star_or",
    "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, star((h1 : \{heap}) => p(h1) || q(h1), r, h) == (star(p, r, h) || star(q, r, h))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  let zeros = "pts(mem_length(\{m}), REPLICATE((n : Num), (b : \{w8})))"
  let star_grow = lemma(
    "star_grow",
    "∀ p : \{hprop}, ∀ r : \{hprop}, ∀ m : \{mem_ty}, ∀ n : Num, ∀ b : \{w8}, star(p, r, heap_of(m)) → star(star(p, pts(mem_length(m), REPLICATE(n, b))), r, heap_of(mem_append(m, n, b)))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "star(star((p : \{hprop}), (r : \{hprop})), \{zeros}, heap_of(mem_append(\{m}, n, b)))",
        seq([
          @simp.rewrite_tac(ths([heap_append])),
          @tactics.match_mp_tac(star_intro),
          @simp.asm_rewrite_tac(ths([heap_disj, thm("pts")])),
        ]),
      ),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths([thm("star_assoc")])),
      @tactics.subst1_tac(@bool.ispecl(@list.List([tm(zeros), tm("(r : \{hprop})")]), thm("star_comm"))),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let grow_some = lemma(
    "mem_grow_some",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ m2 : \{mem_ty}, mem_grow(m, n) == SOME(m2) → m2 == mem_append(m, n * Ki64, zero_byte)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([@wasm.thm("mem_grow")])),
      @class.cond_cases_tac,
      @simp.rewrite_tac(ths(opt)),
      @meson.meson_tac(ths([])),
    ]),
  )
  let rb = @bool.conjuncts_rule(@wasm.thm("reduce_base_rules")).to_array()
  let lfill = @wasm.thm("lfill")
  let v_to_e = @wasm.thm("v_to_e")
  let jth = "(j : Num)"
  let mem = "EL(\{jth}, s_mems((s : Wstore)))"
  let ms = "mem_length(\{mem})"
  let pages = "word(DIV(\{ms}, 65536))"
  let unwind = @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv))
  // memory.size
  let size = "Basic(Memory_size)"
  let arity = prove_arities("memory_size", size, 0)
  let prefix = @bool.gen_all(prove_prefix("memory_size", [], size, arity))
  let cases = @wasm.step_cases(s, f, tm("[\{size}]"), compute=false)
  let size_val = "[Basic(EConstNum(ConstInt32(\{pages})))]"
  let size_step = lemma(
    "memory_size_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ j : Num, smem_ind(f_inst(f)) == SOME(j) → reduce_base(s, f, [\{size}], s, f, \{size_val})",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(rb[26]),
      unwind,
      @tactics.exists_tac(tm(jth)),
      @simp.asm_rewrite_tac(ths([@wasm.thm("mem_size"), @wasm.thm("Ki64")])),
    ]),
  )
  let size_cases = lemma(
    "memory_size_cases",
    "∀ s : Wstore, ∀ f : Wframe, ∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, [\{size}], s2, f2, es2) → (∀ j : Num, smem_ind(f_inst(f)) == SOME(j) → s2 == s && f2 == f && es2 == \{size_val})",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
      @simp.asm_rewrite_tac(ths(opt)),
      unwind,
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.asm_rewrite_tac(ths([@wasm.thm("mem_size"), @wasm.thm("Ki64")])),
    ]),
  )
  let _ = lemma(
    "sl_memory_size",
    "∀ p : \{sassn}, sl_triple(p, [Memory_size], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(word(DIV(ms, 65536))))]) && p(vs0, ls, gs, ms, h)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.rewrite_tac(ths([@lists.map()])),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            @tactics.exists_tac(s),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs : List[Value])), \{size_val})")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs : List[Value]), NIL)"), tm("[\{size}]"), s, f, tm(size_val)]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(size_step),
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm(jth), @drule.match_mp(size_cases)(th)))),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([@equal.gsym(v_to_e), thm("map_snoc")])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @simp.rewrite_tac(ths(lift_facts())),
            @tactics.exists_tac(tm(jth)),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.exists_tac(tm("(vs : List[Value])")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  // memory.grow
  let grow = "Basic(Memory_grow)"
  let c = "Basic(EConstNum(ConstInt32((c : \{w}))))"
  let code = "[\{c}, \{grow}]"
  let arity = prove_arities("memory_grow", grow, 1)
  let prefix = @bool.gen_all(prove_prefix("memory_grow", [c], grow, arity))
  let cases = @wasm.step_cases(s, f, tm(code), compute=false)
  let fail_val = "[Basic(EConstNum(ConstInt32(int32_minus_one)))]"
  let fail_step = lemma(
    "memory_grow_fail_step",
    "∀ s : Wstore, ∀ f : Wframe, ∀ j : Num, ∀ c : \{w}, smem_ind(f_inst(f)) == SOME(j) → reduce_base(s, f, \{code}, s, f, \{fail_val})",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(rb[28]),
      unwind,
      @tactics.exists_tac(tm(jth)),
      @simp.asm_rewrite_tac(ths([])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let post = "(vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], ∃ ms0 : Num, (vs == APPEND(vs0, [V_num(ConstInt32(word(DIV(ms0, 65536))))]) && ms == ms0 + val((c : \{w})) * 65536 && star(p(vs0, ls, gs, ms0), pts(ms0, REPLICATE(val(c) * 65536, word(0))), h)) || (vs == APPEND(vs0, [V_num(ConstInt32(int32_minus_one))]) && ms == ms0 && p(vs0, ls, gs, ms0, h)))"
  let _ = lemma(
    "sl_memory_grow",
    "∀ p : \{sassn}, ∀ c : \{w}, sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(ConstInt32(c))]) && p(vs0, ls, gs, ms, h)), [Memory_grow], \{post})",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("sl_triple"), thm("triple")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(th)),
      @simp.rewrite_tac(ths(lift_facts())),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(
        ths([@lists.map_append(), @lists.map(), v_to_e, @equal.gsym(@lists.append_assoc()), @lists.append()]),
      ),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @simp.rewrite_tac(ths([thm("safe")])),
      @tactics.disj2_tac,
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          // it can always fail
          seq([
            @tactics.exists_tac(s),
            @tactics.exists_tac(f),
            @tactics.exists_tac(tm("APPEND(MAP(v_to_e, (vs0 : List[Value])), \{fail_val})")),
            @tactics.mp_tac(
              @bool.ispecl(
                @list.List([s, f, tm("LBase((vs0 : List[Value]), NIL)"), tm(code), s, f, tm(fail_val)]),
                @wasm.thm("decomp_reduce"),
              ),
            ),
            @simp.rewrite_tac(ths([lfill, @lists.append_nil()])),
            @tactics.disch_then(th => @tactics.match_mp_tac(th)),
            @tactics.match_mp_tac(fail_step),
            @meson.asm_meson_tac(ths([])),
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            @tactics.first_x_assum(th => @tactics.strip_assume_tac(@drule.match_mp(prefix)(th))),
            subst_vars(),
            @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(cases)(th))),
            @simp.asm_rewrite_tac(ths(opt)),
            unwind,
            @simp.asm_rewrite_tac(ths(opt)),
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            @simp.rewrite_tac(ths([@equal.gsym(v_to_e), thm("map_snoc")])),
            @tactics.match_mp_tac(thm("safe_vals")),
            @tactics.first(@list.List([
              // it grew
              solve(seq([
                @tactics.first_x_assum(th => @tactics.mp_tac(@drule.match_mp(grow_some)(th))),
                @tactics.disch_then(th => @tactics.subst1_tac(th)),
                @simp.rewrite_tac(ths(lift_facts() + [star_or, thm("s_mems_update_get"), thm("length_list_update"), thm("gvals_mems_update")])),
                @tactics.exists_tac(tm(jth)),
                @simp.asm_simp_tac(ths([thm("el_list_update")])),
                @tactics.exists_tac(tm("(vs0 : List[Value])")),
                @tactics.exists_tac(tm(ms)),
                @tactics.disj1_tac,
                @simp.rewrite_tac(ths([length_append, @wasm.thm("mem_size"), @wasm.thm("Ki64"), @wasm.thm("zero_byte")])),
                @tactics.match_mp_tac(star_grow),
                @simp.asm_rewrite_tac(ths([])),
              ])),
              // it failed
              solve(seq([
                @simp.rewrite_tac(ths(lift_facts() + [star_or])),
                @tactics.exists_tac(tm(jth)),
                @simp.asm_rewrite_tac(ths([])),
                @tactics.exists_tac(tm("(vs0 : List[Value])")),
                @tactics.exists_tac(tm(ms)),
                @tactics.disj2_tac,
                @simp.asm_rewrite_tac(ths([])),
              ])),
            ])),
          ]),
        ]),
      ),
    ]),
  )
}
