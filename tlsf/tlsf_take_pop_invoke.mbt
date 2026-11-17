///|
fn prove_tlsf_take_pop_invoke() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let z = i("word(0)")
  let addr = "sfunc_ind((inst : Inst), (pop : Num))"
  let zeros = "[\{z}, \{z}, \{z}, \{z}]"
  let gspec = "tlsf_proved_spec(\{addr}, tlsf_pop_code((d : \{w})), \{zeros}, 1, 0)"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let lc = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let bins = "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let after = "APPEND((us : \{lw}), (vs : \{lw}))"
  let nbins = "tlsf_bins((d : \{w}), tlsf_pop_fl((hd : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), \{after}), tlsf_pop_sb(hd, sb, \{after}), tlsf_pop_bl(hd, (bl : \{bt}), \{after}))"
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      s = "star(\{ps[k]}, \{s})"
    }
    s
  }
  let p = "(gs : List[Value]) => (ms : Num) => \{star([cell("m","hd"),bins])}"
  let q = "(gs : List[Value]) => (ms : Num) => \{star([cell("m","hd"),cell("word_add((m : " + w + "), word(8))","tlsf_prev((us : " + lw + "))"),cell("word_add((m : " + w + "), word(12))","tlsf_hd((vs : " + lw + "))"),nbins])}"
  let spec = inst(thm("tlsf_pop_call"), [
    "(d : \{w})",
    addr,
    "(m : \{w})",
    "(hd : \{w})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(us : \{lw})",
    "(vs : \{lw})",
    "(fp : \{rty})",
  ])
  let atoms = @basics.conjuncts(@basics.dest_imp(@kernel.concl(spec)).0)
    .to_array()
    .map(@kernel.assume_rule)
  let spec = @bool.mp(spec, @bool.conj(atoms[0], atoms[1]))
  let spec = @simp.rewrite_rule(
    ths([thm("tlsf_pop_pre"), thm("tlsf_pop_post")]),
  )(spec)
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ m : \{w}, ∀ n : \{w}, ∀ hd : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let cond = "16 <= val(tlsf_size((hd : \{w}))) && (bl : \{bt})(tlsf_level_of(hd))(tlsf_slot_of(hd)) == APPEND((us : \{lw}), CONS((m : \{w}), (vs : \{lw})))"
  let rws = [thm("tlsf_pop_pre"), thm("tlsf_pop_post")]
  let vc = seq([
    gen,
    rw(rws),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
  ])
  let raw = sym_prove(
    "tlsf_pop_invoke_g",
    "\{vars}, \{cond} → sl_triple_g(\{gspec}, fs, tabs, inst, \{falsep}, st(NIL, \{lc}, \{p}), [Local_get(0), Call(pop)], st(NIL, \{lc}, \{q}), NIL)",
    [],
    () => Array::make(2, vc),
    specs=[spec],
    calls=[(0, [])],
    rws~,
  )
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf([T_num(T_i32)], NIL), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_pop_code((d : \{w})))"
  let holds = inst(thm("tlsf_proved_specs"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    addr,
    "tlsf_pop_code((d : \{w}))",
    zeros,
    "[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)]",
    "[T_num(T_i32)]",
    "(NIL : List[Valtype])",
  ])
  let holds = @equal.conv_rule(
    @calc_num.num_reduce_conv,
    @simp.rewrite_rule(ths([@lists.length()]))(holds),
  )
  let _ = lemma(
    "tlsf_pop_invoke",
    "\{vars}, \{native} && \{cond} → sl_triple_m(fs, tabs, inst, st(NIL, \{lc}, \{p}), [Local_get(0), Call(pop)], st(NIL, \{lc}, \{q}), NIL)",
    () => {
      seq([
        gen,
        strip,
        @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
        @tactics.exists_tac(tm(gspec)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.match_mp_tac(holds),
              arw([
                thm("tlsf_pop_call_free"),
                @wasm.thm("n_zeros"),
                @wasm.thm("bitzero"),
                @wasm.thm("bitzero_num"),
                @wasm.thm("those"),
                @wasm.thm("map_option"),
                @lists.map(),
              ]),
            ]),
            seq([@tactics.match_mp_tac(raw), arw([])]),
          ]),
        ),
      ])
    },
  )
}
