// Refine memory.grow's two semantic outcomes before running its abort guard.

///|
fn prove_tlsf_initialize_grow_result() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let before = "(before : \{heap})"
  let fp = "(fp : \{rty})"
  let req = "tlsf_initialize_required(\{d})"
  let old = "(word(DIV(\{lim},65536)) : \{w})"
  let delta = "word_sub(\{req},\{old})"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("tlsf_base("+d+")")},\{i(req)},\{i(old)}]"
  let saved = "tlsf_initialize_saved(\{d},\{lim},\{before},\{fp})"
  let fresh = "tlsf_initialize_fresh(\{d},\{lim},\{fp})"
  let failure = "st([\{i("word(4294967295)")}],\{lc},\{saved})"
  let success = "st([\{i(old)}],\{lc},\{fresh})"
  let post = "(vs : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (\{failure})(vs,ls,gs,ms,h) || (\{success})(vs,ls,gs,ms,h)"
  let raw = inst(thm("st_memory_grow"), [
    "(NIL : List[Value])", lc, lim, saved, delta,
  ])
  let valid = "tlsf_initialize_valid(\{d},\{lim})"
  let cond = "word_ugt(\{req},\{old})"
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_initialize_memory_grow",
    "\{vars}, \{valid} && \{cond} → sl_triple_m(\{env},st([\{i(delta)}],\{lc},\{saved}),[Memory_grow],\{post},NIL)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_growth_delta"), [d, lim])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_initialize_limit_cases"), [d, lim])),
      arw([]),
      strip,
      @tactics.undisch_tac(tm(valid)),
      rw([thm("tlsf_initialize_valid")]),
      strip,
      initialize_m_conseq(
        raw,
        seq([
          gen,
          rw([thm("st"), thm("tlsf_initialize_saved"), @lists.append()]),
          @meson.meson_tac(ths([])),
        ]),
        seq([
          gen,
          beta_goal(),
          rw([thm("st"), thm("tlsf_initialize_fresh"), @lists.append()]),
          strip,
          subst_vars(),
          @tactics.first(
            @list.List([
              solve(arw([])),
              solve(
                seq([
                  @tactics.disj2_tac,
                  arw([]),
                  @tactics.mp_tac(
                    inst(thm("tlsf_initialize_grown_zero_frame"), [
                      d,
                      lim,
                      "val(\{delta})*65536",
                      before,
                      fp,
                      "(gs : List[Value])",
                      "(h : \{heap})",
                    ]),
                  ),
                  arw([]),
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  )
}
