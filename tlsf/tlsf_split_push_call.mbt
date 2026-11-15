///|
fn prove_tlsf_split_push_call() -> Unit raise {
  let w = w32
  let bt = "(Num) -> (Num) -> List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let h = "(hd : \{w})"
  let f = "(word_sub(word(27), word(word_clz(tlsf_size(\{h})))) : \{w})"
  let j = "word_and(word_jushr(tlsf_size(\{h}), \{f}), word(15))"
  def("tlsf_push_fl", "tlsf_push_fl(\{h}, (fl : \{w})) == word_or(fl, word_jshl(word(1), \{f}))")
  def("tlsf_push_sb", "tlsf_push_sb(\{h}, (sb : (Num) -> \{w})) == tlsf_upd(sb, val(\{f}), word_or(sb(val(\{f})), word_jshl(word(1), \{j})))")
  def("tlsf_push_bl", "tlsf_push_bl(\{h}, (m : \{w}), (bl : \{bt})) == tlsf_upd(bl, val(\{f}), tlsf_upd(bl(val(\{f})), val(\{j}), CONS(m, bl(val(\{f}))(val(\{j})))) )")
  let cell = (a : String, x : String) => "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  let at = (a : String, k : String) => "word_add((\{a} : \{w}), word(\{k}))"
  let rpre = "(gs : List[Value]) => (ms : Num) => star(\{cell("m", "hd")}, star(\{cell(at("m", "8"), "pf0")}, star(\{cell(at("m", "12"), "nf0")}, star(tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})), (fp : \{rty})(gs, ms)))))"
  let rpost = "(gs : List[Value]) => (ms : Num) => star(\{cell("m", "hd")}, star(tlsf_bins((d : \{w}), tlsf_push_fl((hd : \{w}), (fl : \{w})), tlsf_push_sb(hd, (sb : (Num) -> \{w})), tlsf_push_bl(hd, (m : \{w}), (bl : \{bt}))), (fp : \{rty})(gs, ms)))"
  let p = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [V_num(ConstInt32((m : \{w})))] && (\{rpre})(gs, ms, h)"
  let q = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == [V_num(ConstInt32((word(0) : \{w})))] && (\{rpost})(gs, ms, h)"
  def("tlsf_push_pre", "tlsf_push_pre((d : \{w}), (m : \{w}), \{h}, (pf0 : \{w}), (nf0 : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (fp : \{rty})) == (\{p})")
  def("tlsf_push_post", "tlsf_push_post((d : \{w}), (m : \{w}), \{h}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (fp : \{rty})) == (\{q})")
  let pre = "tlsf_push_pre((d : \{w}), (m : \{w}), \{h}, (pf0 : \{w}), (nf0 : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (fp : \{rty}))"
  let post = "tlsf_push_post((d : \{w}), (m : \{w}), \{h}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (fp : \{rty}))"
  let zs = "[V_num(ConstInt32((word(0) : \{w}))), V_num(ConstInt32((word(0) : \{w}))), V_num(ConstInt32((word(0) : \{w})))]"
  let rws = [thm("tlsf_push_pre"), thm("tlsf_push_post"), thm("tlsf_push_fl"), thm("tlsf_push_sb"), thm("tlsf_push_bl"), thm("tlsf_size"), @lists.append()]
  let path = inst(thm("tlsf_push_all"), ["(d : \{w})", "(m : \{w})", h, "(pf0 : \{w})", "(nf0 : \{w})", "(fl : \{w})", "(sb : (Num) -> \{w})", "(bl : \{bt})", "(fp : \{rty})"])
  let vars = "∀ d : \{w}, ∀ addr : Num, ∀ m : \{w}, ∀ hd : \{w}, ∀ pf0 : \{w}, ∀ nf0 : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}"
  let _ = lemma("tlsf_push_call", "\{vars}, !(m == word(0)) && 16 <= val(tlsf_size(hd)) → tlsf_proved_spec(addr, tlsf_push_code(d), \{zs}, 1, 1, addr, \{pre}, \{post})", seq([
    gen, strip, @tactics.rule_assum_tac(@simp.rewrite_rule(ths([thm("tlsf_size")]))), rw([thm("tlsf_proved_spec")]),
    @tactics.repeat_tac(@tactics.conj_tac),
    @tactics.first(@list.List([
      solve(seq([
        @tactics.gen_tac,
        by_path(path, "T", rws, [], rws, []),
      ])),
      solve(seq([gen, rw(rws), @tactics.repeat_tac(@tactics.strip_tac), subst_vars(), rw([@lists.length()]), @tactics.conv_tac(@calc_num.num_reduce_conv)])),
    ])),
  ]))
}
