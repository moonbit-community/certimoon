// Loads and stores against points-to: what a WasmCert memory holds where
// star(pts(a, bs), r) describes it.
//
// - read_pts: the bytes at a are bs, inside the memory;
// - load_pts: so a load of LENGTH(bs) bytes at n + off = a gives bs;
// - heap_of_write: writing bs at a changes only a .. a + LENGTH(bs) - 1;
// - write_pts: so after writing bs' (as long as bs) the memory is
//   star(pts(a, bs'), r): the frame r still holds.

///|
fn prove_memory() -> Unit raise {
  let take = @wasm.thm("take")
  let drop = @wasm.thm("drop")
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  let defs = [
    take,
    drop,
    @lists.length(),
    @lists.el(),
    @lists.hd(),
    @lists.tl(),
    @arith.le_suc(),
    @arith.lt_suc(),
    @nums.suc_inj(),
    @arith.add_clauses(),
    @arith.lt(),
    @nums.not_suc(),
  ]
  // arithmetic first: MESON failing on an arithmetic goal is slow
  let finish = @tactics.try_tac(
    @tactics.orelse_tac(@int.asm_arith_tac, @meson.asm_meson_tac(ths([]))),
  )
  // induction on the list, then on n, then cases on i (when `on_i`)
  let induction = (on_i : Bool) => seq([
    @lists.list_induct_tac,
    @nums.induct_tac,
    if on_i {
      seq([
        @tactics.gen_tac,
        @tactics.struct_cases_tac(@bool.spec(tm("(i : Num)"), @nums.num_cases())),
      ])
    } else {
      @tactics.all_tac
    },
    @simp.asm_rewrite_tac(ths(defs)),
    finish,
  ])
  let length_take = lemma(
    "length_take",
    "∀ l : List[A], ∀ n : Num, n <= LENGTH(l) → LENGTH(take(n, l)) == n",
    induction(false),
  )
  let el_take = lemma(
    "el_take",
    "∀ l : List[A], ∀ n : Num, ∀ i : Num, i < n && n <= LENGTH(l) → EL(i, take(n, l)) == EL(i, l)",
    induction(true),
  )
  let length_drop = lemma(
    "length_drop",
    "∀ l : List[A], ∀ n : Num, LENGTH(drop(n, l)) == LENGTH(l) - n",
    induction(false),
  )
  let el_drop = lemma(
    "el_drop",
    "∀ l : List[A], ∀ n : Num, ∀ i : Num, n + i < LENGTH(l) → EL(i, drop(n, l)) == EL(n + i, l)",
    seq([
      @lists.list_induct_tac,
      @nums.induct_tac,
      @tactics.gen_tac,
      @simp.asm_rewrite_tac(ths(defs)),
      finish,
    ]),
  )
  let read_bytes = @wasm.thm("read_bytes")
  let m = "(m : \{mem_ty})"
  let read_length = lemma(
    "read_bytes_length",
    "∀ m : \{mem_ty}, ∀ a : Num, ∀ n : Num, a + n <= LENGTH(SND(m)) → LENGTH(read_bytes(m, a, n)) == n",
    seq([
      @simp.rewrite_tac(ths([read_bytes])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(length_take),
      @simp.rewrite_tac(ths([length_drop])),
      @int.asm_arith_tac,
    ]),
  )
  let read_el = lemma(
    "read_bytes_el",
    "∀ m : \{mem_ty}, ∀ a : Num, ∀ n : Num, ∀ i : Num, a + n <= LENGTH(SND(m)) && i < n → EL(i, read_bytes(m, a, n)) == EL(a + i, SND(m))",
    seq([
      @simp.rewrite_tac(ths([read_bytes])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(@bool.ispecl(@list.List([tm("drop((a : Num), SND(\{m}))"), tm("(n : Num)"), tm("(i : Num)")]), el_take)),
      @tactics.mp_tac(@bool.ispecl(@list.List([tm("SND(\{m})"), tm("(a : Num)"), tm("(i : Num)")]), el_drop)),
      @simp.rewrite_tac(ths([length_drop])),
      have("(a : Num) + (i : Num) < LENGTH(SND(\{m}))", @int.asm_arith_tac),
      have("(n : Num) <= LENGTH(SND(\{m})) - (a : Num)", @int.asm_arith_tac),
      @simp.asm_rewrite_tac(ths([])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let star = thm("star")
  let pts = thm("pts")
  let pts_at = lemma(
    "pts_at",
    "∀ a : Num, ∀ bs : List[\{w8}], ∀ r : \{hprop}, ∀ h : \{heap}, ∀ x : Num, star(pts(a, bs), r)(h) && a <= x && x < a + LENGTH(bs) → h(x) == SOME(EL(x - a, bs))",
    seq([
      @simp.rewrite_tac(ths([star, pts])),
      @tactics.repeat_tac(@tactics.strip_tac),
      subst_vars(),
      @simp.rewrite_tac(ths([thm("hunion"), thm("pts_heap")])),
      @simp.asm_rewrite_tac(ths(opt)),
    ]),
  )
  let heap_of = thm("heap_of")
  let _ = lemma(
    "read_pts",
    "∀ a : Num, ∀ bs : List[\{w8}], ∀ r : \{hprop}, ∀ m : \{mem_ty}, star(pts(a, bs), r)(heap_of(m)) && !(bs == NIL) → a + LENGTH(bs) <= LENGTH(SND(m)) && read_bytes(m, a, LENGTH(bs)) == bs",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      // the bytes of bs are in m
      have(
        "∀ x : Num, (a : Num) <= x && x < a + LENGTH((bs : List[\{w8}])) → x < LENGTH(SND(\{m})) && EL(x, SND(m)) == EL(x - a, bs)",
        seq([
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.mp_tac(
            @bool.ispecl(
              @list.List([tm("(a : Num)"), tm("(bs : List[\{w8}])"), tm("(r : \{hprop})"), tm("heap_of(\{m})"), tm("(x : Num)")]),
              pts_at,
            ),
          ),
          @simp.asm_rewrite_tac(ths([heap_of])),
          @class.cond_cases_tac,
          @simp.asm_rewrite_tac(ths(opt)),
        ]),
      ),
      have(
        "(a : Num) + LENGTH((bs : List[\{w8}])) <= LENGTH(SND(\{m}))",
        seq([
          @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(a : Num) + LENGTH((bs : List[\{w8}])) - 1"), th))),
          @tactics.undisch_tac(tm("!((bs : List[\{w8}]) == NIL)")),
          @simp.rewrite_tac(ths([@equal.gsym(@lists.length_eq_nil())])),
          @meson.meson_tac(ths([arith("∀ a : Num, ∀ n : Num, ∀ k : Num, !(n == 0) && (a <= a + n - 1 && a + n - 1 < a + n → a + n - 1 < k) → a + n <= k")])),
        ]),
      ),
      @simp.asm_rewrite_tac(ths([@lists.list_eq()])),
      @simp.asm_simp_tac(ths([read_length])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.mp_tac(
        @bool.ispecl(@list.List([tm(m), tm("(a : Num)"), tm("LENGTH((bs : List[\{w8}]))"), tm("(n : Num)")]), read_el),
      ),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.disch_then(th => @tactics.subst1_tac(th)),
      @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(a : Num) + (n : Num)"), th))),
      @simp.rewrite_tac(ths([arith("∀ a : Num, ∀ n : Num, a + n - a == n")])),
      @meson.asm_meson_tac(ths([arith("∀ a : Num, ∀ n : Num, ∀ k : Num, n < k → a <= a + n && a + n < a + k")])),
    ]),
  )
  prove_write(length_take, el_take, length_drop, el_drop, opt)
  prove_load_store()
}

///|
/// The rules' memory functions: WasmCert's load and store at n + off.
fn prove_load_store() -> Unit raise {
  let takefill = @wasm.thm("takefill")
  let takefill_length = lemma(
    "takefill_length",
    "∀ l : List[A], ∀ a : A, takefill(a, LENGTH(l), l) == l",
    seq([@lists.list_induct_tac, @simp.asm_rewrite_tac(ths([takefill, @lists.length()]))]),
  )
  let defs = ths([@wasm.thm("load"), @wasm.thm("store"), @wasm.thm("mem_length"), @wasm.thm("bytes_takefill"), takefill_length])
  let read = (a : String) => @tactics.mp_tac(
    @bool.ispecl(
      @list.List([tm(a), tm("(bs : List[\{w8}])"), tm("(r : \{hprop})"), tm("(m : \{mem_ty})")]),
      thm("read_pts"),
    ),
  )
  let _ = lemma(
    "load_pts",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ off : Num, ∀ bs : List[\{w8}], ∀ r : \{hprop}, star(pts(n + off, bs), r)(heap_of(m)) && !(bs == NIL) → load(m, n, off, LENGTH(bs)) == SOME(bs)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      read("(n : Num) + (off : Num)"),
      @simp.asm_rewrite_tac(defs),
      @tactics.strip_tac,
      @simp.asm_rewrite_tac(defs),
    ]),
  )
  let _ = lemma(
    "store_pts",
    "∀ m : \{mem_ty}, ∀ n : Num, ∀ off : Num, ∀ bs : List[\{w8}], ∀ bs2 : List[\{w8}], ∀ r : \{hprop}, star(pts(n + off, bs), r)(heap_of(m)) && LENGTH(bs2) == LENGTH(bs) && !(bs == NIL) → store(m, n, off, bs2, LENGTH(bs2)) == SOME(write_bytes(m, n + off, bs2)) && star(pts(n + off, bs2), r)(heap_of(write_bytes(m, n + off, bs2)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            read("(n : Num) + (off : Num)"),
            @simp.asm_rewrite_tac(defs),
            @tactics.strip_tac,
            @simp.asm_rewrite_tac(defs),
          ]),
          seq([
            @tactics.match_mp_tac(thm("write_pts")),
            @tactics.exists_tac(tm("(bs : List[\{w8}])")),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
}

///|
fn prove_write(
  length_take : @kernel.Thm,
  el_take : @kernel.Thm,
  length_drop : @kernel.Thm,
  el_drop : @kernel.Thm,
  opt : Array[@kernel.Thm],
) -> Unit raise {
  let l = "(l : List[A])"
  let bs = "(bs : List[A])"
  let new = "APPEND(take((a : Num), \{l}), APPEND(\{bs}, drop(a + LENGTH(\{bs}), \{l})))"
  let take_a = have(
    "LENGTH(take((a : Num), \{l})) == a",
    seq([@tactics.match_mp_tac(length_take), @int.asm_arith_tac]),
  )
  let length_write = lemma(
    "length_write",
    "∀ l : List[A], ∀ a : Num, ∀ bs : List[A], a + LENGTH(bs) <= LENGTH(l) → LENGTH(\{new}) == LENGTH(l)",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      take_a,
      @simp.asm_rewrite_tac(ths([@lists.length_append(), length_drop])),
      @int.asm_arith_tac,
    ]),
  )
  let el_append = @lists.el_append()
  let el_write = lemma(
    "el_write",
    "∀ l : List[A], ∀ a : Num, ∀ bs : List[A], ∀ x : Num, a + LENGTH(bs) <= LENGTH(l) && x < LENGTH(l) → EL(x, \{new}) == (if a <= x && x < a + LENGTH(bs) { EL(x - a, bs) } else { EL(x, l) })",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      take_a,
      @simp.rewrite_tac(ths([el_append])),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.thenl(
        @class.asm_cases_tac(tm("(x : Num) < (a : Num)")),
        @list.List([
          // before the written bytes
          seq([
            have("!((a : Num) <= (x : Num))", @int.asm_arith_tac),
            @simp.asm_rewrite_tac(ths([])),
            @tactics.match_mp_tac(el_take),
            @int.asm_arith_tac,
          ]),
          @tactics.thenl(
            @class.asm_cases_tac(tm("(x : Num) - (a : Num) < LENGTH(\{bs})")),
            @list.List([
              // the written bytes
              seq([
                have("(a : Num) <= (x : Num) && x < a + LENGTH(\{bs})", @int.asm_arith_tac),
                @simp.asm_rewrite_tac(ths([])),
              ]),
              // after them
              seq([
                have("!((x : Num) < (a : Num) + LENGTH(\{bs}))", @int.asm_arith_tac),
                @simp.asm_rewrite_tac(ths([])),
                @tactics.mp_tac(
                  @bool.ispecl(
                    @list.List([tm(l), tm("(a : Num) + LENGTH(\{bs})"), tm("(x : Num) - (a : Num) - LENGTH(\{bs})")]),
                    el_drop,
                  ),
                ),
                have("(a : Num) + LENGTH(\{bs}) + ((x : Num) - a - LENGTH(bs)) == x", @int.asm_arith_tac),
                @simp.asm_rewrite_tac(ths([])),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let w8l = "(bs : List[\{w8}])"
  let m = "(m : \{mem_ty})"
  let heap_of = thm("heap_of")
  let fun_eq = @class.fun_eq_thm()
  let heap_of_write = lemma(
    "heap_of_write",
    "∀ m : \{mem_ty}, ∀ a : Num, ∀ bs : List[\{w8}], a + LENGTH(bs) <= LENGTH(SND(m)) → heap_of(write_bytes(m, a, bs)) == ((x : Num) => if a <= x && x < a + LENGTH(bs) { SOME(EL(x - a, bs)) } else { heap_of(m)(x) })",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.rewrite_tac(ths([@wasm.thm("write_bytes"), heap_of, fun_eq, @pair.snd()])),
      @tactics.gen_tac,
      @simp.asm_simp_tac(ths([length_write])),
      @tactics.thenl(
        @class.asm_cases_tac(tm("(x : Num) < LENGTH(SND(\{m}))")),
        @list.List([
          seq([
            @simp.asm_simp_tac(ths([el_write])),
            @class.cond_cases_tac,
            @simp.asm_rewrite_tac(ths([])),
          ]),
          seq([
            have("!((x : Num) < (a : Num) + LENGTH(\{w8l}))", @int.asm_arith_tac),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        ]),
      ),
    ]),
  )
  let pts_heap = thm("pts_heap")
  let pts_heap_none = lemma(
    "pts_heap_none",
    "∀ a : Num, ∀ bs : List[\{w8}], ∀ x : Num, pts_heap(a, bs)(x) == NONE == !(a <= x && x < a + LENGTH(bs))",
    seq([
      @simp.rewrite_tac(ths([pts_heap])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @class.cond_cases_tac,
      @simp.asm_rewrite_tac(ths(opt)),
    ]),
  )
  let _ = lemma(
    "write_pts",
    "∀ a : Num, ∀ bs : List[\{w8}], ∀ bs2 : List[\{w8}], ∀ r : \{hprop}, ∀ m : \{mem_ty}, star(pts(a, bs), r)(heap_of(m)) && LENGTH(bs2) == LENGTH(bs) && !(bs == NIL) → star(pts(a, bs2), r)(heap_of(write_bytes(m, a, bs2)))",
    seq([
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(a : Num) + LENGTH((bs2 : List[\{w8}])) <= LENGTH(SND(\{m}))",
        seq([
          @tactics.mp_tac(
            @bool.ispecl(
              @list.List([tm("(a : Num)"), tm(w8l), tm("(r : \{hprop})"), tm(m)]),
              thm("read_pts"),
            ),
          ),
          @simp.asm_rewrite_tac(ths([])),
          @meson.meson_tac(ths([])),
        ]),
      ),
      @simp.asm_simp_tac(ths([heap_of_write])),
      @tactics.undisch_tac(tm("star(pts((a : Num), \{w8l}), (r : \{hprop}))(heap_of(\{m}))")),
      @simp.rewrite_tac(ths([thm("star"), thm("pts")])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.exists_tac(tm("pts_heap((a : Num), (bs2 : List[\{w8}]))")),
      @tactics.exists_tac(tm("(h2 : \{heap})")),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.undisch_tac(tm("hdisj((h1 : \{heap}), (h2 : \{heap}))")),
      @simp.asm_rewrite_tac(ths([thm("hdisj"), pts_heap_none, thm("hunion"), fun_eq])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.mp_tac(@bool.spec(tm("(x : Num)"), th))),
      @simp.rewrite_tac(ths([pts_heap])),
      @tactics.repeat_tac(@tactics.then_tac(@class.cond_cases_tac, @simp.asm_rewrite_tac(ths(opt)))),
    ]),
  )
}

///|
/// pts_split: the bytes xs ++ ys at a are xs at a and, beside them, ys
/// after xs.
fn prove_pts_split() -> Unit raise {
  let pts_heap = thm("pts_heap")
  let opt = [
    @ind_types.option_distinct(),
    @equal.gsym(@ind_types.option_distinct()),
    @ind_types.option_inj(),
  ]
  let disj = lemma(
    "pts_heap_disj",
    "∀ a : Num, ∀ xs : List[\{w8}], ∀ ys : List[\{w8}], hdisj(pts_heap(a, xs), pts_heap(a + LENGTH(xs), ys))",
    seq([
      @simp.rewrite_tac(ths([thm("hdisj"), thm("pts_heap_none")])),
      @int.arith_tac,
    ]),
  )
  let union = lemma(
    "pts_heap_append",
    "∀ a : Num, ∀ xs : List[\{w8}], ∀ ys : List[\{w8}], pts_heap(a, APPEND(xs, ys)) == hunion(pts_heap(a, xs), pts_heap(a + LENGTH(xs), ys))",
    seq([
      @simp.rewrite_tac(ths([@class.fun_eq_thm(), thm("hunion"), pts_heap, @lists.length_append(), @lists.el_append()])),
      @tactics.repeat_tac(@tactics.gen_tac),
      // which of the two ranges x is in
      @class.asm_cases_tac(tm("(a : Num) <= (x : Num) && x < a + LENGTH((xs : List[\{w8}]))")),
      @class.asm_cases_tac(tm("(a : Num) + LENGTH((xs : List[\{w8}])) <= (x : Num) && x < a + LENGTH(xs) + LENGTH((ys : List[\{w8}]))")),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.repeat_tac(@class.cond_cases_tac),
      @simp.asm_rewrite_tac(ths(opt + [arith("∀ x : Num, ∀ a : Num, ∀ b : Num, x - a - b == x - (a + b)")])),
      @tactics.try_tac(@int.asm_arith_tac),
    ]),
  )
  let _ = lemma(
    "pts_split",
    "∀ a : Num, ∀ xs : List[\{w8}], ∀ ys : List[\{w8}], pts(a, APPEND(xs, ys)) == star(pts(a, xs), pts(a + LENGTH(xs), ys))",
    seq([
      @simp.rewrite_tac(ths([thm("pts"), thm("star")])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.abs_tac,
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
      @simp.rewrite_tac(ths([disj, union])),
    ]),
  )
}
