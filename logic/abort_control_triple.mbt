///|
fn prove_abort_control_triples() -> Unit raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst"
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let keep = (p : String, stack : String) => {
    "keep(\{env},lift(\{p},(fr : \{hprop})),(s : Wstore),(f : Wframe),\{stack})"
  }
  let st = "st((v : List[Value]),(lc : List[Value]),(R : \{rty}))"
  let sn = "st((NIL : List[Value]),(lc : List[Value]),(R : \{rty}))"
  let _ = lemma(
    "abort_st_heap",
    "∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, st(v,l,R,vs,lc,gs,ms) == ((h : \{heap}) => vs == v && lc == l && R(gs,ms,h))",
    seq([gen, rw([@class.fun_eq_thm()]), gen, rw([thm("st")])]),
  )
  let _ = lemma(
    "abort_keep_st_values",
    "\{vars}, ∀ v : List[Value], ∀ lc : List[Value], ∀ R : \{rty}, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], \{keep(st,"(vs : List[Value])")} → vs == v",
    seq([
      rw([thm("keep"), thm("abort_st_heap")] + lift_facts()),
      @tactics.repeat_tac(@tactics.strip_tac),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "abort_keep_st_transport",
    "\{vars}, ∀ v : List[Value], ∀ lc : List[Value], ∀ R : \{rty}, ∀ fr : \{hprop}, ∀ s : Wstore, ∀ f : Wframe, ∀ vs : List[Value], \{keep(st,"(vs : List[Value])")} → \{keep(sn,"NIL")}",
    seq([
      rw([thm("keep"), thm("abort_st_heap")] + lift_facts()),
      @tactics.repeat_tac(@tactics.strip_tac),
      @meson.asm_meson_tac(ths([])),
    ]),
  )
  let ent = "∀ vs : List[Value], ∀ lc2 : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, \{sn}(vs,lc2,gs,ms,h) → (A : \{sassn})(vs,lc2,gs,ms,h)"
  let _ = lemma(
    "sl_abort_unreachable_m",
    "\{vars}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ Q : \{sassn}, ∀ A : \{sassn}, (\{ent}) → sl_abort_m(\{env},\{sn},[Unreachable],Q,A)",
    seq([
      rw([thm("sl_abort_m")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(vs : List[Value]) == NIL",
        @meson.asm_meson_tac(ths([thm("abort_keep_st_values")])),
      ),
      subst_vars(),
      rw([@lists.map(), @lists.append()]),
      @tactics.match_mp_tac(thm("safe_abort_unreachable")),
      beta_goal(),
      @meson.asm_meson_tac(ths([thm("abort_keep_lift_mono")])),
    ]),
  )
  let _ = lemma(
    "sl_abort_block_st_m",
    "\{vars}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ bs : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, sl_abort_m(\{env},\{sn},bs,Q,A) → sl_abort_m(\{env},\{sn},[Block(Tbv(NONE),bs)],Q,A)",
    seq([
      rw([thm("sl_abort_m")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(vs : List[Value]) == NIL",
        @meson.asm_meson_tac(ths([thm("abort_keep_st_values")])),
      ),
      subst_vars(),
      rw([@lists.map(), @lists.append()]),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @tactics.first(
        @list.List([
          solve(rw([thm("safe_abort")])),
          solve(
            seq([
              @tactics.match_mp_tac(thm("safe_abort_unit_block")),
              @tactics.first_x_assum(th => {
                @tactics.match_mp_tac(
                  @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
                    @bool.ispecl(
                      @list.List(
                        [
                          "(fr : \{hprop})",
                          "(s : Wstore)",
                          "(f : Wframe)",
                          "(NIL : List[Value])",
                          "(n' : Num)",
                        ].map(tm),
                      ),
                      th,
                    ),
                  ),
                )
              }),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let i = "V_num(ConstInt32((c : \{w32})))"
  let code = "[If(Tbv(NONE),(bs1 : List[B_e]),(bs2 : List[B_e]))]"
  let bp = (bs : String) => {
    "sl_abort_m(\{env},\{sn},[Block(Tbv(NONE),\{bs})],(Q : \{sassn}),(A : \{sassn}))"
  }
  let _ = lemma(
    "sl_abort_if_blocks_m",
    "\{vars}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ c : \{w32}, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, (!(c == word(0)) → \{bp("bs1")}) && (c == word(0) → \{bp("bs2")}) → sl_abort_m(\{env},st([\{i}],lc,R),\{code},Q,A)",
    seq([
      rw([thm("sl_abort_m")]),
      @tactics.repeat_tac(@tactics.strip_tac),
      have(
        "(vs : List[Value]) == [\{i}]",
        @meson.asm_meson_tac(ths([thm("abort_keep_st_values")])),
      ),
      have(
        keep(sn, "NIL"),
        @meson.asm_meson_tac(ths([thm("abort_keep_st_transport")])),
      ),
      subst_vars(),
      rw([@lists.map(), @lists.append(), @wasm.thm("v_to_e")]),
      @tactics.struct_cases_tac(@bool.spec(tm("(n : Num)"), @nums.num_cases())),
      @tactics.first(
        @list.List([
          solve(rw([thm("safe_abort")])),
          solve(
            seq([
              @tactics.match_mp_tac(thm("safe_abort_unit_if")),
              @tactics.conj_tac,
              @tactics.disch_tac,
              @tactics.first_x_assum(branch => {
                @tactics.first_assum(condition => {
                  let body = @bool.mp(branch, condition)
                  let point = @bool.ispecl(
                    @list.List(
                      [
                        "(fr : \{hprop})",
                        "(s : Wstore)",
                        "(f : Wframe)",
                        "(NIL : List[Value])",
                        "(n' : Num)",
                      ].map(tm),
                    ),
                    body,
                  )
                  @tactics.match_mp_tac(
                    @simp.rewrite_rule(ths([@lists.map(), @lists.append()]))(
                      point,
                    ),
                  )
                })
              }),
              arw([]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let body = (bs : String) => {
    "sl_abort_m(\{env},\{sn},\{bs},(Q : \{sassn}),(A : \{sassn}))"
  }
  let _ = lemma(
    "sl_abort_if_st_m",
    "\{vars}, ∀ lc : List[Value], ∀ R : \{rty}, ∀ c : \{w32}, ∀ bs1 : List[B_e], ∀ bs2 : List[B_e], ∀ Q : \{sassn}, ∀ A : \{sassn}, (!(c == word(0)) → \{body("bs1")}) && (c == word(0) → \{body("bs2")}) → sl_abort_m(\{env},st([\{i}],lc,R),\{code},Q,A)",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("sl_abort_if_blocks_m")),
      @meson.asm_meson_tac(ths([thm("sl_abort_block_st_m")])),
    ]),
  )
}
