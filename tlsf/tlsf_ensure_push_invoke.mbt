///|
fn prove_tlsf_ensure_push_invoke() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let z = i("word(0)")
  let addr = "sfunc_ind((inst : Inst), (push : Num))"
  let zeros = "[\{z}, \{z}, \{z}]"
  let gspec = "tlsf_proved_spec(\{addr}, tlsf_push_code((d : \{w})), \{zeros}, 1, 1)"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let lc = "(lc0 : List[Value])"
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let bins = "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let nbins = "tlsf_bins((d : \{w}), tlsf_push_fl((hd : \{w}), (fl : \{w})), tlsf_push_sb(hd, (sb : (Num) -> \{w})), tlsf_push_bl(hd, (m : \{w}), (bl : \{bt})))"
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      s = "star(\{ps[k]}, \{s})"
    }
    s
  }
  let p = "(gs : List[Value]) => (ms : Num) => \{star([cell("m","hd"),cell("word_add((m : " + w + "),word(8))","pf0"),cell("word_add((m : " + w + "),word(12))","nf0"),bins])}"
  let q = "(gs : List[Value]) => (ms : Num) => \{star([cell("m","hd"),nbins])}"
  let spec = inst(thm("tlsf_push_call"), [
    "(d : \{w})",
    addr,
    "(m : \{w})",
    "(hd : \{w})",
    "(pf0 : \{w})",
    "(nf0 : \{w})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
  ])
  let atoms = @basics.conjuncts(@basics.dest_imp(@kernel.concl(spec)).0)
    .to_array()
    .map(@kernel.assume_rule)
  let spec = @bool.mp(spec, @bool.conj(atoms[0], atoms[1]))
  let spec = @simp.rewrite_rule(
    ths([thm("tlsf_push_pre"), thm("tlsf_push_post")]),
  )(spec)
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ m : \{w}, ∀ lc0 : List[Value], ∀ hd : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ pf0 : \{w}, ∀ nf0 : \{w}, ∀ fp : \{rty}"
  let cond = "!((m : \{w}) == word(0)) && 16 <= val(tlsf_size((hd : \{w})))"
  let rws = [thm("tlsf_push_pre"), thm("tlsf_push_post")]
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
    "tlsf_ensure_push_invoke_g",
    "\{vars}, \{cond} → sl_triple_g(\{gspec}, fs, tabs, inst, \{falsep}, st([\{i("m")}], \{lc}, \{p}), [Call(push), Drop], st(NIL, \{lc}, \{q}), NIL)",
    [],
    Array::make(2, vc),
    specs=[spec],
    calls=[(0, [])],
    rws~,
  )
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let holds = inst(thm("tlsf_proved_specs"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    addr,
    "tlsf_push_code((d : \{w}))",
    zeros,
    "[T_num(T_i32),T_num(T_i32),T_num(T_i32)]",
    "[T_num(T_i32)]",
    "[T_num(T_i32)]",
  ])
  let holds = @equal.conv_rule(
    @calc_num.num_reduce_conv,
    @simp.rewrite_rule(ths([@lists.length()]))(holds),
  )
  let _ = lemma(
    "tlsf_ensure_push_invoke",
    "\{vars}, \{native} && \{cond} → sl_triple_m(fs, tabs, inst, st([\{i("m")}], \{lc}, \{p}), [Call(push), Drop], st(NIL, \{lc}, \{q}), NIL)",
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
              thm("tlsf_push_call_free"),
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
    ]),
  )
}
