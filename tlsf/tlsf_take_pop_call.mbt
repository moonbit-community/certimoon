///|
fn prove_tlsf_take_pop_call() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{v} : \{w})))"
  }
  let star = (ps : Array[String]) => {
    let mut acc = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      acc = "star(\{ps[k]}, \{acc})"
    }
    acc
  }
  let after = "APPEND((us : \{lw}), (vs : \{lw}))"
  let bins = "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let nbins = "tlsf_bins((d : \{w}), tlsf_pop_fl((hd : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), \{after}), tlsf_pop_sb(hd, sb, \{after}), tlsf_pop_bl(hd, (bl : \{bt}), \{after}))"
  let h = cell("m", "hd")
  let pre = "(args : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => args == [V_num(ConstInt32((m : \{w})))] && \{star([h,bins])}(h)"
  let post = "(res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => res == NIL && \{star([h, cell("word_add((m : " + w + "), word(8))", "tlsf_prev((us : " + lw + "))"), cell("word_add((m : " + w + "), word(12))", "tlsf_hd((vs : " + lw + "))"), nbins])}(h)"
  let args = "(d : \{w}), (m : \{w}), (hd : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (us : \{lw}), (vs : \{lw}), (fp : \{rty})"
  def("tlsf_pop_pre", "tlsf_pop_pre(\{args}) == (\{pre})")
  def("tlsf_pop_post", "tlsf_pop_post(\{args}) == (\{post})")
  let z = "V_num(ConstInt32((word(0) : \{w})))"
  let zeros = "[\{z}, \{z}, \{z}, \{z}]"
  let rws = [
    thm("tlsf_pop_pre"),
    thm("tlsf_pop_post"),
    thm("tlsf_pop_fl"),
    thm("tlsf_pop_sb"),
    thm("tlsf_pop_bl"),
    thm("tlsf_size"),
    thm("tlsf_level_of"),
    thm("tlsf_slot_of"),
    @lists.append(),
  ]
  let path = inst(thm("tlsf_pop_all"), [
    "(d : \{w})",
    "(m : \{w})",
    "(hd : \{w})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(us : \{lw})",
    "(vs : \{lw})",
    "(fp : \{rty})",
  ])
  let _ = lemma(
    "tlsf_pop_call",
    "∀ d : \{w}, ∀ addr : Num, ∀ m : \{w}, ∀ hd : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ fp : \{rty}, 16 <= val(tlsf_size(hd)) && bl(tlsf_level_of(hd))(tlsf_slot_of(hd)) == APPEND(us, CONS(m, vs)) → tlsf_proved_spec(addr, tlsf_pop_code(d), \{zeros}, 1, 0, addr, tlsf_pop_pre(\{args}), tlsf_pop_post(\{args}))",
    () => {
      seq([
        gen,
        strip,
        @tactics.rule_assum_tac(@simp.rewrite_rule(ths(rws))),
        rw([thm("tlsf_proved_spec")]),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(seq([@tactics.gen_tac, by_path(path, "T", rws, [], rws, [])])),
            solve(
              seq([
                gen,
                rw(rws),
                @tactics.repeat_tac(@tactics.strip_tac),
                subst_vars(),
                rw([@lists.length()]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_pop_call_free",
    "∀ d : \{w}, call_free_b(tlsf_pop_code(d))",
    () => seq([gen, call_free_tac()]),
  )
  ignore(arw)
}
