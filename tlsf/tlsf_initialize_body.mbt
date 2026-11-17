// Composition of the exact initializer, including its checked abort path.

///|
fn prove_tlsf_initialize_body() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w32})"
  let lim = "(lim : Num)"
  let before = "(before : \{heap})"
  let fp = "(fp : \{rty})"
  let es = [
    "(fs : List[Cl])", "(tabs : List[(Tab_t,List[V_ref])])", "(inst : Inst)",
  ]
  let env = es.join(",")
  let saved = "tlsf_initialize_saved(\{d},\{lim},\{before},\{fp})"
  let fresh = "tlsf_initialize_fresh(\{d},\{lim},\{fp})"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w32})))"
  let z = i("word(0)")
  let lc1 = "[\{i("tlsf_base("+d+")")},\{i("tlsf_initialize_required("+d+")")},\{z}]"
  let lc2 = "[\{i("tlsf_base("+d+")")},\{i("tlsf_initialize_required("+d+")")},\{i("word(DIV("+lim+",65536))")}]"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(\{d}))"
  let pre = "tlsf_initialize_pre(\{d},\{lim},\{before},\{fp})"
  let post = "tlsf_initialize_post(\{d},\{lim},\{before},\{fp})"
  let abortp = "tlsf_initialize_abort(\{d},\{lim},\{before},\{fp})"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w32}, ∀ push : Num, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  let arithmetic = inst(thm("tlsf_initialize_arithmetic_raw"), [
    d, "(push : Num)", z, z, saved, z,
  ])
  let _ = lemma(
    "tlsf_initialize_body_saved",
    "\{vars}, tlsf_initialize_valid(d,lim) && \{native} → sl_abort_m(\{env},st(NIL,[\{z},\{z},\{z}],\{saved}),tlsf_initialize_code(d,push),\{body_post(post)},\{abortp})",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_initialize_parts")]),
        @tactics.match_mp_tac(thm("sl_abort_seq_m")),
        @tactics.exists_tac(tm("st(NIL,\{lc1},\{saved})")),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_abort_conseq(arithmetic, same_tac(), same_tac()),
            seq([
              @tactics.match_mp_tac(thm("sl_abort_seq_m")),
              @tactics.exists_tac(tm("st(NIL,\{lc2},\{saved})")),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  @tactics.match_accept_tac(thm("tlsf_initialize_check_saved")),
                  seq([
                    @tactics.match_mp_tac(thm("sl_abort_seq_m")),
                    @tactics.exists_tac(tm("st(NIL,\{lc2},\{fresh})")),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        seq([
                          @tactics.match_mp_tac(
                            thm("tlsf_initialize_grow_saved"),
                          ),
                          arw([]),
                        ]),
                        seq([
                          @tactics.match_mp_tac(
                            thm("tlsf_initialize_tail_fresh"),
                          ),
                          arw([]),
                        ]),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
  let path = inst(
    thm("tlsf_initialize_body_saved"),
    es + [d, "(push : Num)", lim, before, fp],
  )
  let _ = lemma(
    "tlsf_initialize_body",
    "\{vars}, tlsf_initialize_valid(d,lim) && \{native} → sl_abort_m(\{env},st(NIL,[\{z},\{z},\{z}],(gs : List[Value]) => (ms : Num) => (h : \{heap}) => \{pre}(NIL,gs,ms,h)),tlsf_initialize_code(d,push),\{body_post(post)},\{abortp})",
    () => {
      seq([
        gen,
        strip,
        initialize_abort_conseq(
          path,
          seq([
            gen,
            rw([
              thm("st"),
              thm("tlsf_initialize_pre"),
              thm("tlsf_initialize_saved"),
            ]),
            @meson.asm_meson_tac(ths([])),
          ]),
          same_tac(),
        ),
      ])
    },
  )
}
