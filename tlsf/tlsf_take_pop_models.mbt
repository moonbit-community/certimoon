///|
fn prove_tlsf_take_pop_models() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let h = "(hd : \{w})"
  let f = "(word_sub(word(27), word(word_clz(tlsf_size(\{h})))) : \{w})"
  let j = "word_and(word_jushr(tlsf_size(\{h}), \{f}), word(15))"
  let flip = "word_xor((sb : (Num) -> \{w})(val(\{f})), word_jshl((word(1) : \{w}), \{j}))"
  def(
    "tlsf_pop_fl",
    "tlsf_pop_fl(\{h}, (fl : \{w}), (sb : (Num) -> \{w}), (xs : \{lw})) == (if xs == NIL { if \{flip} == word(0) { word_xor(fl, word_jshl(word(1), \{f})) } else { fl } } else { fl })",
  )
  def(
    "tlsf_pop_sb",
    "tlsf_pop_sb(\{h}, (sb : (Num) -> \{w}), (xs : \{lw})) == tlsf_upd(sb, val(\{f}), (if xs == NIL { \{flip} } else { sb(val(\{f})) }))",
  )
  def(
    "tlsf_pop_bl",
    "tlsf_pop_bl(\{h}, (bl : \{bt}), (xs : \{lw})) == tlsf_upd(bl, val(\{f}), tlsf_upd(bl(val(\{f})), val(\{j}), xs))",
  )
  let ht = "(\{w}) -> \{w}"
  let _ = lemma(
    "tlsf_mark_other",
    "∀ hd : \{ht}, ∀ m : \{w}, ∀ x : \{w}, !(x == m) → tlsf_mark(hd, m, x) == hd(x)",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        rw([thm("tlsf_mark"), thm("tlsf_put")]),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_mark_used",
    "∀ hd : \{ht}, ∀ m : \{w}, tlsf_used(tlsf_mark(hd, m, m))",
    () => {
      seq([
        gen,
        rw([thm("tlsf_mark"), thm("tlsf_put")]),
        @tactics.mp_tac(
          inst(thm("tlsf_used_store_fields"), ["(hd : \{ht})((m : \{w}))"]),
        ),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_count_append",
    "∀ xs : \{lw}, ∀ ys : \{lw}, ∀ m : \{w}, tlsf_count(m, APPEND(xs, ys)) == tlsf_count(m, xs) + tlsf_count(m, ys)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_count"), @lists.filter_append(), @lists.length_append()]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_remove_other_count",
    "∀ us : \{lw}, ∀ vs : \{lw}, ∀ m : \{w}, ∀ x : \{w}, !(x == m) → tlsf_count(x, APPEND(us, CONS(m, vs))) == tlsf_count(x, APPEND(us, vs))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        arw([thm("tlsf_count_append"), thm("tlsf_count_cons")]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_remove_self_count",
    "∀ us : \{lw}, ∀ vs : \{lw}, ∀ m : \{w}, tlsf_count(m, APPEND(us, CONS(m, vs))) == 1 → tlsf_count(m, APPEND(us, vs)) == 0",
    () => {
      seq([
        gen,
        rw([thm("tlsf_count_append"), thm("tlsf_count_cons")]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @int.arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_pop_bl_other_count",
    "∀ hd : \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ m : \{w}, ∀ x : \{w}, ∀ i : Num, ∀ k : Num, bl(tlsf_level_of(hd))(tlsf_slot_of(hd)) == APPEND(us, CONS(m, vs)) && !(x == m) → tlsf_count(x, tlsf_pop_bl(hd, bl, APPEND(us, vs), i, k)) == tlsf_count(x, bl(i)(k))",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_pop_bl"), thm("tlsf_upd")]),
        @class.asm_cases_tac(tm("(i : Num) == tlsf_level_of((hd : \{w}))")),
        @class.asm_cases_tac(tm("(k : Num) == tlsf_slot_of((hd : \{w}))")),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(ths([thm("tlsf_level_of"), thm("tlsf_slot_of")])),
        ),
        arw([]),
        @tactics.mp_tac(
          inst(thm("tlsf_remove_other_count"), [
            "(us : \{lw})",
            "(vs : \{lw})",
            "(m : \{w})",
            "(x : \{w})",
          ]),
        ),
        arw([]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
}
