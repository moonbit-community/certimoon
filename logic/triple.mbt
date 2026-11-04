// Triples over WasmCert's reduction relation.
//
// - safe(n, s, f, es, q): for n steps, every run of (s, f, es) either has
//   ended in values vs with q(s, f, vs), or can step, and every step is
//   safe for one step less. A trap cannot step and is not a value, so a
//   safe configuration does not trap; memory.grow's choice is covered,
//   since every step is.
// - triple(p, bs, q): from a value stack vs with p(s, f, vs), the
//   instructions bs are safe for every n: partial correctness, no traps.
// - sl_triple(p, bs, q): p and q describe the value stack, the locals and
//   the globals as heap assertions on the current memory, and the triple
//   holds with any frame r beside them (lift(p, r): on the memory the
//   instance uses), so the frame rule is a lemma.
// - gvals(s, f): the values of the instance's globals, by index. lift also
//   asks that the instance's global addresses are in the store and
//   distinct (globs_ok), so setting one global changes no other.

///|
/// An assertion on a configuration: store, frame, value stack.
let assn : String = "(Wstore, Wframe, List[Value]) -> Bool"

///|
/// A separation assertion: on the value stack, the locals and the globals,
/// a heap assertion.
let sassn : String = "(List[Value], List[Value], List[Value], \{heap}) -> Bool"

///|
fn define_triples() -> Unit raise {
  def(
    "safe",
    "safe(0, (s : Wstore), (f : Wframe), (es : List[Einstr]), (q : \{assn})) == true && safe(SUC(n), s, f, es, q) == ((∃ vs : List[Value], es == MAP(v_to_e, vs) && q(s, f, vs)) || ((∃ s2 : Wstore, ∃ f2 : Wframe, ∃ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2)) && (∀ s2 : Wstore, ∀ f2 : Wframe, ∀ es2 : List[Einstr], reduce(s, f, es, s2, f2, es2) → safe(n, s2, f2, es2, q))))",
  )
  def(
    "triple",
    "triple((p : \{assn}), (bs : List[B_e]), (q : \{assn})) == (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ n : Num, p(s, f, vs) → safe(n, s, f, APPEND(MAP(v_to_e, vs), MAP(Basic, bs)), q))",
  )
  def(
    "gvals",
    "gvals((s : Wstore), (f : Wframe)) == MAP((a : Num) => g_val(EL(a, s_globs(s))), inst_globs(f_inst(f)))",
  )
  def(
    "globs_ok",
    "globs_ok((s : Wstore), (f : Wframe)) == (∀ i : Num, i < LENGTH(inst_globs(f_inst(f))) → EL(i, inst_globs(f_inst(f))) < LENGTH(s_globs(s)) && (∀ k : Num, k < LENGTH(inst_globs(f_inst(f))) && EL(k, inst_globs(f_inst(f))) == EL(i, inst_globs(f_inst(f))) → k == i))",
  )
  def(
    "lift",
    "lift((p : \{sassn}), (r : \{hprop}), (s : Wstore), (f : Wframe), (vs : List[Value])) == (∃ j : Num, smem_ind(f_inst(f)) == SOME(j) && j < LENGTH(s_mems(s)) && globs_ok(s, f) && star(p(vs, f_locs(f), gvals(s, f)), r, heap_of(EL(j, s_mems(s)))))",
  )
  def(
    "sl_triple",
    "sl_triple((p : \{sassn}), (bs : List[B_e]), (q : \{sassn})) == (∀ r : \{hprop}, triple(lift(p, r), bs, lift(q, r)))",
  )
}

///|
fn prove_triples() -> Unit raise {
  let safe = thm("safe")
  let triple = thm("triple")
  let lift = thm("lift")
  let sl_triple = thm("sl_triple")
  let num_cases = (v : String) => @tactics.struct_cases_tac(
    @bool.spec(tm("(\{v} : Num)"), @nums.num_cases()),
  )
  let safe_vals = lemma(
    "safe_vals",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ q : \{assn}, q(s, f, vs) → safe(n, s, f, MAP(v_to_e, vs), q)",
    seq([
      @tactics.gen_tac,
      num_cases("n"),
      @simp.rewrite_tac(ths([safe])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let safe_mono = lemma(
    "safe_mono",
    "∀ n : Num, ∀ s : Wstore, ∀ f : Wframe, ∀ es : List[Einstr], ∀ q : \{assn}, ∀ q2 : \{assn}, (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) && safe(n, s, f, es, q) → safe(n, s, f, es, q2)",
    @tactics.thenl(
      @nums.induct_tac,
      @list.List([
        @simp.rewrite_tac(ths([safe])),
        seq([
          @simp.rewrite_tac(ths([safe])),
          @tactics.repeat_tac(@tactics.strip_tac),
          @tactics.orelse_tac(
            seq([
              @tactics.disj1_tac,
              @tactics.exists_tac(tm("(vs : List[Value])")),
              @meson.asm_meson_tac(ths([])),
            ]),
            seq([
              @tactics.disj2_tac,
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @meson.asm_meson_tac(ths([])),
                  seq([
                    @tactics.repeat_tac(@tactics.strip_tac),
                    @tactics.first_x_assum(th => @tactics.match_mp_tac(th)),
                    @tactics.exists_tac(tm("(q : \{assn})")),
                    @meson.asm_meson_tac(ths([])),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      ]),
    ),
  )
  let triple_conseq = lemma(
    "triple_conseq",
    "∀ p : \{assn}, ∀ p2 : \{assn}, ∀ bs : List[B_e], ∀ q : \{assn}, ∀ q2 : \{assn}, (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], p2(s, f, vs) → p(s, f, vs)) && triple(p, bs, q) && (∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], q(s, f, vs) → q2(s, f, vs)) → triple(p2, bs, q2)",
    seq([@simp.rewrite_tac(ths([triple])), @meson.meson_tac(ths([safe_mono]))]),
  )
  let star_mono = thm("star_mono")
  let lift_mono = lemma(
    "lift_mono",
    "∀ p : \{sassn}, ∀ p2 : \{sassn}, ∀ r : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], ∀ vs2 : List[Value], (∀ ls : List[Value], ∀ gs : List[Value], ∀ h : \{heap}, p(vs, ls, gs, h) → p2(vs2, ls, gs, h)) && lift(p, r, s, f, vs) → lift(p2, r, s, f, vs2)",
    seq([
      @simp.rewrite_tac(ths([lift])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.exists_tac(tm("(j : Num)")),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.match_mp_tac(star_mono),
      @tactics.exists_tac(tm("(p : \{sassn})(vs, f_locs(f), gvals(s, f))")),
      @tactics.exists_tac(tm("(r : \{hprop})")),
      @simp.asm_rewrite_tac(ths([])),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let map_snoc = lemma(
    "map_snoc",
    "∀ vs : List[Value], ∀ v : Value, APPEND(MAP(v_to_e, vs), [v_to_e(v)]) == MAP(v_to_e, APPEND(vs, [v]))",
    @simp.rewrite_tac(ths([@lists.map_append(), @lists.map()])),
  )
  let _ = lemma(
    "sl_conseq",
    "∀ p : \{sassn}, ∀ p2 : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ q2 : \{sassn}, (∀ vs : List[Value], ∀ ls : List[Value], ∀ gs : List[Value], ∀ h : \{heap}, p2(vs, ls, gs, h) → p(vs, ls, gs, h)) && sl_triple(p, bs, q) && (∀ vs : List[Value], ∀ ls : List[Value], ∀ gs : List[Value], ∀ h : \{heap}, q(vs, ls, gs, h) → q2(vs, ls, gs, h)) → sl_triple(p2, bs, q2)",
    seq([
      @simp.rewrite_tac(ths([sl_triple])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(triple_conseq),
      @tactics.exists_tac(tm("lift((p : \{sassn}), (r : \{hprop}))")),
      @tactics.exists_tac(tm("lift((q : \{sassn}), (r : \{hprop}))")),
      @simp.asm_rewrite_tac(ths([])),
      @tactics.conj_tac,
      @tactics.repeat_tac(@tactics.strip_tac),
      @tactics.match_mp_tac(lift_mono),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let fun_eq = @class.fun_eq_thm()
  let lift_frame = lemma(
    "lift_frame",
    "∀ p : \{sassn}, ∀ fr : \{hprop}, ∀ r : \{hprop}, lift((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => star(p(vs, ls, gs), fr), r) == lift(p, star(fr, r))",
    seq([
      @simp.rewrite_tac(ths([fun_eq, lift, thm("star_assoc")])),
    ]),
  )
  let _ = lemma(
    "sl_frame",
    "∀ p : \{sassn}, ∀ bs : List[B_e], ∀ q : \{sassn}, ∀ fr : \{hprop}, sl_triple(p, bs, q) → sl_triple((vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => star(p(vs, ls, gs), fr), bs, (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => star(q(vs, ls, gs), fr))",
    seq([
      @simp.rewrite_tac(ths([sl_triple, lift_frame])),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "sl_const",
    "∀ p : \{sassn}, ∀ c : V_num, sl_triple(p, [EConstNum(c)], (vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => ∃ vs0 : List[Value], vs == APPEND(vs0, [V_num(c)]) && p(vs0, ls, gs, h))",
    seq([
      @simp.rewrite_tac(ths([sl_triple, triple])),
      @tactics.repeat_tac(@tactics.strip_tac),
      @simp.rewrite_tac(ths([@lists.map(), @equal.gsym(@wasm.thm("v_to_e"))])),
      @simp.rewrite_tac(ths([map_snoc])),
      @tactics.match_mp_tac(safe_vals),
      @tactics.match_mp_tac(lift_mono),
      @tactics.exists_tac(tm("(p : \{sassn})")),
      @tactics.exists_tac(tm("(vs : List[Value])")),
      @simp.asm_rewrite_tac(ths([])),
      @meson.meson_tac(ths([])),
    ]),
  )
}
