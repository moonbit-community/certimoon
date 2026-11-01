// Separation logic on linear memory: heaps (what each address holds),
// separating conjunction, points-to, and the heap a WasmCert memory is.
//
// - hdisj(h1, h2): no address is in both; hunion(h1, h2): both together.
// - star(p, q): the heap splits into disjoint parts, p of one and q of
//   the other; emp: the empty heap.
// - pts(a, bs): exactly the bytes bs at a, a + 1, ...
// - heap_of(m): memory m's bytes at addresses 0 .. mem_length(m) - 1.
//
// The lemmas connect them to WasmCert's memory functions: a load reads the
// bytes a points-to gives (load_pts), and a store changes only them, so
// what holds of the rest of memory still does (store_pts).

///|
fn define_heap() -> Unit raise {
  def(
    "hdisj",
    "hdisj((h1 : \{heap}), (h2 : \{heap})) == (∀ x : Num, h1(x) == NONE || h2(x) == NONE)",
  )
  def(
    "hunion",
    "hunion((h1 : \{heap}), (h2 : \{heap})) == ((x : Num) => if h1(x) == NONE { h2(x) } else { h1(x) })",
  )
  def(
    "star",
    "star((p : \{hprop}), (q : \{hprop})) == ((h : \{heap}) => ∃ h1 : \{heap}, ∃ h2 : \{heap}, hdisj(h1, h2) && h == hunion(h1, h2) && p(h1) && q(h2))",
  )
  def("emp", "emp == ((h : \{heap}) => ∀ x : Num, h(x) == NONE)")
  def(
    "pts_heap",
    "pts_heap(a, (bs : List[\{w8}])) == ((x : Num) => if a <= x && x < a + LENGTH(bs) { SOME(EL(x - a, bs)) } else { NONE })",
  )
  def("pts", "pts(a, (bs : List[\{w8}])) == ((h : \{heap}) => h == pts_heap(a, bs))")
  def(
    "heap_of",
    "heap_of((m : \{mem_ty})) == ((x : Num) => if x < LENGTH(SND(m)) { SOME(EL(x, SND(m))) } else { NONE })",
  )
}

///|
let x_num : String = "(x : Num)"

///|
/// For the goal `∀ x. ...` after rewriting: case on each `if`, then
/// rewrite with the assumptions and decide the arithmetic.
fn pointwise(extra : Array[@kernel.Thm]) -> @tactics.Tactic raise {
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.repeat_tac(@tactics.then_tac(@class.cond_cases_tac, @simp.asm_rewrite_tac(ths(extra)))),
    @tactics.try_tac(@simp.asm_rewrite_tac(ths(extra))),
  ])
}

///|
/// Cases on whether each heap holds nothing at x.
fn cases_none(heaps : Array[String]) -> @tactics.Tactic raise {
  seq(
    heaps.map(fn(h) raise {
      @class.asm_cases_tac(tm("(\{h} : \{heap})((x : Num)) == NONE"))
    }),
  )
}

///|
fn prove_heap() -> Unit raise {
  let fun_eq = @class.fun_eq_thm()
  let opt = [@ind_types.option_distinct(), @equal.gsym(@ind_types.option_distinct()), @ind_types.option_inj()]
  let hdisj = thm("hdisj")
  let hunion = thm("hunion")
  let star = thm("star")
  let hdisj_sym = lemma(
    "hdisj_sym",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, hdisj(h1, h2) == hdisj(h2, h1)",
    seq([@simp.rewrite_tac(ths([hdisj])), @meson.meson_tac(ths([]))]),
  )
  let hunion_none = lemma(
    "hunion_none",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, ∀ x : Num, hunion(h1, h2)(x) == NONE == (h1(x) == NONE && h2(x) == NONE)",
    seq([@simp.rewrite_tac(ths([hunion])), pointwise(opt)]),
  )
  let hunion_comm = lemma(
    "hunion_comm",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, hdisj(h1, h2) → hunion(h1, h2) == hunion(h2, h1)",
    seq([
      @simp.rewrite_tac(ths([hdisj, hunion, fun_eq])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.first_x_assum(th => @tactics.disj_cases_tac(@bool.spec(tm(x_num), th))),
      @simp.asm_rewrite_tac(ths(opt)),
      @tactics.try_tac(@tactics.then_tac(@class.cond_cases_tac, @simp.asm_rewrite_tac(ths(opt)))),
    ]),
  )
  let hdisj_union = lemma(
    "hdisj_union",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, ∀ h3 : \{heap}, hdisj(hunion(h1, h2), h3) == (hdisj(h1, h3) && hdisj(h2, h3))",
    seq([@simp.rewrite_tac(ths([hdisj, hunion_none])), @meson.meson_tac(ths([]))]),
  )
  let hdisj_union_r = lemma(
    "hdisj_union_r",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, ∀ h3 : \{heap}, hdisj(h1, hunion(h2, h3)) == (hdisj(h1, h2) && hdisj(h1, h3))",
    seq([@simp.rewrite_tac(ths([hdisj, hunion_none])), @meson.meson_tac(ths([]))]),
  )
  let hunion_assoc = lemma(
    "hunion_assoc",
    "∀ h1 : \{heap}, ∀ h2 : \{heap}, ∀ h3 : \{heap}, hunion(hunion(h1, h2), h3) == hunion(h1, hunion(h2, h3))",
    seq([
      @simp.rewrite_tac(ths([hunion, fun_eq])),
      @tactics.repeat_tac(@tactics.gen_tac),
      cases_none(["h1", "h2"]),
      @simp.asm_rewrite_tac(ths(opt)),
    ]),
  )
  // a split of h into hunion(a, b), and of b or a again: the witnesses
  let ex = (ts : Array[String]) => seq(ts.map(t => @tactics.exists_tac(tm(t.replace_all(old="@", new=": \{heap}")))))
  let facts = ths([hdisj_sym, hunion_comm])
  let _ = lemma(
    "star_comm",
    "∀ p : \{hprop}, ∀ q : \{hprop}, star(p, q) == star(q, p)",
    seq([
      @simp.rewrite_tac(ths([star, fun_eq])),
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.eq_tac,
      @tactics.repeat_tac(@tactics.strip_tac),
      ex(["(h2 @)", "(h1 @)"]),
      @meson.asm_meson_tac(facts),
    ]),
  )
  // after the witnesses, each conjunct is an assumption, or follows by
  // splitting the disjointness of unions, or by associativity
  let finish = seq([
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([hdisj_union, hdisj_union_r]))),
    @simp.asm_rewrite_tac(ths([hunion_assoc, hdisj_union, hdisj_union_r])),
  ])
  let _ = lemma(
    "star_assoc",
    "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ r : \{hprop}, star(star(p, q), r) == star(p, star(q, r))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([star])),
      @tactics.abs_tac,
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.thenl(
        @tactics.eq_tac,
        @list.List([
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            ex(["(h1' @)", "hunion((h2' @), (h2 @))"]),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.try_tac(ex(["(h2' @)", "(h2 @)"])),
            finish,
          ]),
          seq([
            @tactics.repeat_tac(@tactics.strip_tac),
            subst_vars(),
            ex(["hunion((h1 @), (h1' @))", "(h2' @)"]),
            @tactics.repeat_tac(@tactics.conj_tac),
            @tactics.try_tac(ex(["(h1 @)", "(h1' @)"])),
            finish,
          ]),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "star_mono",
    "∀ p : \{hprop}, ∀ p2 : \{hprop}, ∀ q : \{hprop}, ∀ q2 : \{hprop}, ∀ h : \{heap}, (∀ h1 : \{heap}, p(h1) → p2(h1)) && (∀ h2 : \{heap}, q(h2) → q2(h2)) && star(p, q)(h) → star(p2, q2)(h)",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
}
