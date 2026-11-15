// Close the body against the actual native free, pop, and push closures.
// Only free appears in the ambient specs: helper calls were already closed.

///|
fn prove_tlsf_free_module() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value], List[Value], Num, \{heap}) -> Bool"
  let gt = "(Num, \{ft}, \{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let same = seq([gen, beta_goal(), strip, arw([])])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let params = "(d : \{w}), (m : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}), (fp : \{rty})"
  let pv = "∀ m : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ fp : \{rty}"
  let p = "tlsf_free_pre(\{params})"
  let q = "tlsf_free_post(\{params})"
  let zeros = "[\{i("word(0)")},\{i("word(0)")}]"
  let bp = body_pre(p, "(args : List[Value])", zeros)
  let bq = body_post(q)
  let popnative = "EL(sfunc_ind((inst : Inst), (pop : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], NIL), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_pop_code((d : \{w})))"
  let pushnative = "EL(sfunc_ind((inst : Inst), (push : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let env = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num"
  let focused = inst(thm("tlsf_free_body_focused"), [
    "(G : \{gt})",
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t, List[V_ref])])",
    "(inst : Inst)",
    "(d : \{w})",
    "(pop : Num)",
    "(push : Num)",
    "(m : \{w})",
    "(lim : Num)",
    "(top : \{w})",
    "(xs : \{lw})",
    "(hd : \{ht})",
    "(fl : \{w})",
    "(sb : (Num) -> \{w})",
    "(bl : \{bt})",
    "(fp : \{rty})",
  ])
  let fparts = args_of(
    @basics.dest_imp(@kernel.concl(focused)).1,
    "sl_triple_g",
    9,
  ).unwrap()
  let facts = "tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), (xs : \{lw}), (hd : \{ht})) && tlsf_bins_match((xs : \{lw}), (hd : \{ht}), (bl : \{bt})) && tlsf_tables_sync((fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let pure = "MEM((m : \{w}),(xs : \{lw})) && tlsf_used((hd : \{ht})(m)) && \{facts}"
  let pp = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (\{pure}) && (\{show(fparts[5])})(vs,lc,gs,ms,h)"
  let pre = seq([
    gen,
    beta_goal(),
    rw([thm("tlsf_free_pre"), thm("st"), @lists.append()]),
    strip,
    subst_vars(),
    arw([@lists.append()]),
    @tactics.mp_tac(
      inst(thm("tlsf_large_facts_frame"), [
        "(d : \{w})",
        "(lim : Num)",
        "(top : \{w})",
        "(xs : \{lw})",
        "(hd : \{ht})",
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "star(tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd : \{ht})(m)))),(fp : \{rty})((gs : List[Value]),(lim : Num)))",
        "(h : \{heap})",
      ]),
    ),
    @meson.asm_meson_tac(ths([])),
  ])
  let _ = lemma(
    "tlsf_free_body",
    "∀ G : \{gt}, \{env}, \{pv}, ∀ args : List[Value], \{popnative} && \{pushnative} → sl_triple_g(G,fs,tabs,inst,\{bq},\{bp},tlsf_free_code(d,pop,push),\{bq},[\{bq}])",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_conseq_g")),
      @tactics.exists_tac(tm(pp)),
      @tactics.exists_tac(tm(bq)),
      @tactics.exists_tac(tm("[\{bq}]")),
      rw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(pre),
          solve(
            seq([
              @tactics.match_mp_tac(thm("sl_pure_g")),
              strip,
              rw([@class.eta_ax()]),
              @tactics.match_mp_tac(
                @simp.rewrite_rule(ths([@class.eta_ax()]))(focused),
              ),
              arw([]),
            ]),
          ),
          solve(same),
        ]),
      ),
    ]),
  )
  let spec = "tlsf_free_spec((inst : Inst),(d : \{w}),(pop : Num),(push : Num),(free_idx : Num))"
  def(
    "tlsf_free_spec",
    "\{spec}((a : Num),(P : \{ft}),(Q : \{ft})) == (a == sfunc_ind(inst,free_idx) && (∃ m : \{w}, ∃ lim : Num, ∃ top : \{w}, ∃ xs : \{lw}, ∃ hd : \{ht}, ∃ fl : \{w}, ∃ sb : (Num) -> \{w}, ∃ bl : \{bt}, ∃ fp : \{rty}, P == \{p} && Q == \{q}))",
  )
  let spec_call = lemma(
    "tlsf_free_spec_call",
    "∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ free_idx : Num, \{pv}, \{spec}(sfunc_ind(inst,free_idx),\{p},\{q})",
    seq([
      gen,
      rw([thm("tlsf_free_spec")]),
      seq(
        [
          "(m : \{w})",
          "(lim : Num)",
          "(top : \{w})",
          "(xs : \{lw})",
          "(hd : \{ht})",
          "(fl : \{w})",
          "(sb : (Num) -> \{w})",
          "(bl : \{bt})",
          "(fp : \{rty})",
        ].map(x => @tactics.exists_tac(tm(x))),
      ),
      rw([]),
    ]),
  )
  let free_ts = "[T_num(T_i32),T_num(T_i32)]"
  let freenative = "EL(sfunc_ind((inst : Inst),(free_idx : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),\{free_ts},tlsf_free_code((d : \{w}),(pop : Num),(push : Num)))"
  let natives = "\{freenative} && \{popnative} && \{pushnative}"
  let specs = lemma(
    "tlsf_free_specs",
    "\{env}, ∀ free_idx : Num, \{natives} → (∀ k : Num, specs_ok(k,\{spec},fs,tabs,inst))",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_funs_g")),
      gen,
      rw([thm("tlsf_free_spec")]),
      strip,
      subst_vars(),
      seq(
        [
          "[T_num(T_i32)]",
          "[T_num(T_i32)]",
          free_ts,
          "tlsf_free_code((d : \{w}),(pop : Num),(push : Num))",
          zeros,
        ].map(x => @tactics.exists_tac(tm(x))),
      ),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(arw([])),
          solve(
            seq([
              rw([
                @wasm.thm("n_zeros"),
                @wasm.thm("bitzero"),
                @wasm.thm("bitzero_num"),
                @wasm.thm("map_option"),
                @lists.map(),
                @wasm.thm("those"),
              ]),
            ]),
          ),
          solve(
            seq([gen, @tactics.match_mp_tac(thm("tlsf_free_body")), arw([])]),
          ),
          solve(
            seq([
              gen,
              rw([thm("tlsf_free_pre"), thm("tlsf_free_post")]),
              @tactics.repeat_tac(@tactics.strip_tac),
              subst_vars(),
              rw([@lists.length()]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let cp = call_pre(p, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let cq = call_post(q, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let _ = lemma(
    "tlsf_free_all",
    "\{env}, ∀ free_idx : Num, \{pv}, ∀ vs0 : List[Value], ∀ lc0 : List[Value], \{natives} → sl_triple_m(fs,tabs,inst,\{cp},[Call(free_idx)],\{cq},NIL)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
      @tactics.exists_tac(tm(spec)),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([@tactics.match_mp_tac(specs), arw([])]),
          seq([
            @tactics.match_mp_tac(thm("sl_call_g")),
            rw([@class.eta_ax()]),
            @tactics.match_accept_tac(
              @simp.rewrite_rule(ths([@class.eta_ax()]))(spec_call),
            ),
          ]),
        ]),
      ),
    ]),
  )
}
