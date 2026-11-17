// A closed call triple for the compiler's actual Page::allocate closure,
// including the compiled take/pop/push closures it invokes transitively.

///|
fn prove_tlsf_malloc_page_module() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let model = page_model_variables()
  let vs = model + [("s", w), ("before", heap), ("fp", rty)]
  let params = page_arguments(vs)
  let p = "tlsf_malloc_page_pre(" + params + ")"
  let q = "tlsf_malloc_page_post(" + params + ")"
  let pv = page_quantify(vs)
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let spec = "tlsf_malloc_page_spec((inst : Inst),(d : \{w}),(take_idx : Num),(page_idx : Num))"
  let ex = vs.filter(v => v.0 != "d").map(v => "∃ \{v.0} : \{v.1}, ").join("")
  def(
    "tlsf_malloc_page_spec",
    "\{spec}((a : Num),(P : \{ft}),(Q : \{ft})) == (a == sfunc_ind(inst,page_idx) && (\{ex}P == \{p} && Q == \{q}))",
  )
  let ws = vs.filter(v => v.0 != "d").map(v => "(" + v.0 + " : " + v.1 + ")")
  let spec_call = lemma(
    "tlsf_malloc_page_spec_call",
    "∀ inst : Inst, ∀ take_idx : Num, ∀ page_idx : Num, \{pv} \{spec}(sfunc_ind(inst,page_idx),\{p},\{q})",
    () => {
      seq([
        gen,
        rw([thm("tlsf_malloc_page_spec")]),
        seq(ws.map(x => @tactics.exists_tac(tm(x)))),
        rw([]),
      ])
    },
  )
  let ts = "[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)]"
  let zs = "[" +
    Array::make(5, "V_num(ConstInt32((word(0) : " + w + ")))").join(",") +
    "]"
  let native = "EL(sfunc_ind((inst : Inst),(page_idx : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),\{ts},tlsf_page_allocate_code((take_idx : Num)))"
  let take = inst(thm("tlsf_take_all"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    "(d : " + w + ")",
    "(pop : Num)",
    "(push : Num)",
    "(take_idx : Num)",
    "(word(1080) : " + w + ")",
    "(lim : Num)",
    "(top : " + w + ")",
    "(xs : " + lw + ")",
    "(hd : (" + w + ") -> " + w + ")",
    "(fl : " + w + ")",
    "(sb : (Num) -> " + w + ")",
    "(bl : " + bt + ")",
    "(before : " + heap + ")",
    "(fp : " + rty + ")",
    "(NIL : List[Value])",
    "(NIL : List[Value])",
  ])
  let helpers = show(@basics.dest_imp(@kernel.concl(take)).0)
  let env = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ take_idx : Num, ∀ page_idx : Num"
  let specs = lemma(
    "tlsf_malloc_page_specs",
    "\{env}, \{native} && \{helpers} → (∀ k : Num, specs_ok(k,\{spec},fs,tabs,inst))",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_funs_g")),
        gen,
        rw([thm("tlsf_malloc_page_spec")]),
        strip,
        subst_vars(),
        seq(
          [
            "[T_num(T_i32)]", "[T_num(T_i32)]", ts, "tlsf_page_allocate_code((take_idx : Num))",
            zs,
          ].map(x => @tactics.exists_tac(tm(x))),
        ),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(arw([])),
            solve(
              rw([
                @wasm.thm("n_zeros"),
                @wasm.thm("bitzero"),
                @wasm.thm("bitzero_num"),
                @wasm.thm("map_option"),
                @lists.map(),
                @wasm.thm("those"),
              ]),
            ),
            solve(
              seq([
                gen,
                free_apply(
                  inst(
                    thm("tlsf_malloc_page_body"),
                    [
                      spec, "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])",
                      "(inst : Inst)", "(pop : Num)", "(push : Num)", "(take_idx : Num)",
                    ] +
                    vs.map(v => "(" + v.0 + " : " + v.1 + ")") +
                    ["(args : List[Value])"],
                  ),
                ),
              ]),
            ),
            solve(
              seq([
                gen,
                rw([thm("tlsf_malloc_page_pre"), thm("tlsf_malloc_page_post")]),
                @tactics.repeat_tac(@tactics.strip_tac),
                subst_vars(),
                rw([@lists.length()]),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
  let cp = call_pre(p, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let cq = call_post(q, "(vs0 : List[Value])", "(lc0 : List[Value])")
  let _ = lemma(
    "tlsf_malloc_page_all",
    "\{env}, " +
    page_quantify(
      vs.filter(v => v.0 != "d") +
      [("vs0", "List[Value]"), ("lc0", "List[Value]")],
    ) +
    "\{native} && \{helpers} → sl_triple_m(fs,tabs,inst,\{cp},[Call(page_idx)],\{cq},NIL)",
    () => {
      seq([
        gen,
        strip,
        @logic.match_mp_tac(thm("sl_triple_m_of_g")),
        @tactics.exists_tac(tm(spec)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_apply(
              inst(specs, [
                "(fs : List[Cl])",
                "(tabs : List[(Tab_t,List[V_ref])])",
                "(inst : Inst)",
                "(d : " + w + ")",
                "(pop : Num)",
                "(push : Num)",
                "(take_idx : Num)",
                "(page_idx : Num)",
              ]),
            ),
            seq([
              @logic.match_mp_tac(thm("sl_call_g")),
              rw([@class.eta_ax()]),
              @tactics.match_accept_tac(
                @simp.rewrite_rule(ths([@class.eta_ax()]))(spec_call),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
