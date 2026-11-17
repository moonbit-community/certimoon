///|
fn prove_tlsf_ensure_logic() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let same = seq([gen, beta_goal(), strip, arw([])])
  let r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && (R : \{rty})(gs, ms, h)"
  let p = "st((v : List[Value]), (lc0 : List[Value]), \{r})"
  let q = "st(APPEND((v : List[Value]), [V_num(ConstInt32((word(DIV((lim : Num), 65536)) : \{w})))]), (lc0 : List[Value]), \{r})"
  let raw = inst(thm("sl_memory_size"), [p])
  let terms = args_of(@kernel.concl(raw), "sl_triple", 3).unwrap()
  let _ = lemma(
    "st_memory_size",
    "∀ v : List[Value], ∀ lc0 : List[Value], ∀ lim : Num, ∀ R : \{rty}, sl_triple(\{p}, [Memory_size], \{q})",
    seq([
      gen,
      @tactics.match_mp_tac(thm("sl_conseq")),
      @tactics.exists_tac(terms[0]),
      @tactics.exists_tac(terms[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          same,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @tactics.accept_tac(raw),
              seq([
                gen,
                rw([thm("st")]),
                strip,
                subst_vars(),
                arw([]),
                @meson.asm_meson_tac(ths([])),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let at_p = "st((v : List[Value]),(lc0 : List[Value]),(R : \{rty}))"
  let at_q = "st(APPEND((v : List[Value]),[V_num(ConstInt32((word(DIV((lim : Num),65536)) : \{w})))]),(lc0 : List[Value]),(R : \{rty}))"
  let at_raw = inst(thm("sl_memory_size"), [at_p])
  let at_parts = args_of(@kernel.concl(at_raw), "sl_triple", 3).unwrap()
  let at_cond = "∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, (R : \{rty})(gs,ms,h) → ms == (lim : Num)"
  let _ = lemma(
    "st_memory_size_at",
    "∀ v : List[Value], ∀ lc0 : List[Value], ∀ lim : Num, ∀ R : \{rty}, (\{at_cond}) → sl_triple(\{at_p},[Memory_size],\{at_q})",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_conseq")),
      @tactics.exists_tac(at_parts[0]),
      @tactics.exists_tac(at_parts[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          same,
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @tactics.accept_tac(at_raw),
              seq([gen, rw([thm("st")]), strip, @meson.asm_meson_tac(ths([]))]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lemma(
    "st_heap",
    "∀ v : List[Value], ∀ l : List[Value], ∀ R : \{rty}, ∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, st(v,l,R,vs,lc,gs,ms) == ((h : \{heap}) => vs == v && lc == l && R(gs,ms,h))",
    seq([gen, rw([@class.fun_eq_thm()]), gen, rw([thm("st")])]),
  )
  let c = "(c : \{w})"
  let grow_pre = "st(APPEND((v : List[Value]),[V_num(ConstInt32(\{c}))]),(lc0 : List[Value]),\{r})"
  let oldr = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && (R : \{rty})(gs,lim,h)"
  let newr = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) + val(\{c}) * 65536 && star((R : \{rty})(gs,lim),pts(lim,REPLICATE(val(c)*65536,(word(0) : Word[8]))),h)"
  let neg = "st(APPEND((v : List[Value]),[V_num(ConstInt32((word(4294967295) : \{w})))]),(lc0 : List[Value]),\{oldr})"
  let pos = "st(APPEND((v : List[Value]),[V_num(ConstInt32((word(DIV((lim : Num),65536)) : \{w})))]),(lc0 : List[Value]),\{newr})"
  let grow_post = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (\{neg})(vs,lc,gs,ms,h) || (DIV((lim : Num),65536)+val(\{c}) <= 65536 && (\{pos})(vs,lc,gs,ms,h))"
  let grow = inst(thm("sl_memory_grow"), [p, c])
  let gparts = args_of(@kernel.concl(grow), "sl_triple", 3).unwrap()
  let _ = lemma(
    "st_memory_grow",
    "∀ v : List[Value], ∀ lc0 : List[Value], ∀ lim : Num, ∀ R : \{rty}, ∀ c : \{w}, sl_triple(\{grow_pre},[Memory_grow],\{grow_post})",
    seq([
      gen,
      @tactics.match_mp_tac(thm("sl_conseq")),
      @tactics.exists_tac(gparts[0]),
      @tactics.exists_tac(gparts[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          seq([
            gen,
            rw([thm("st")]),
            strip,
            @tactics.exists_tac(tm("(v : List[Value])")),
            arw([]),
          ]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              @tactics.accept_tac(grow),
              seq([
                gen,
                rw(
                  [
                    thm("st"),
                    thm("st_heap"),
                    @wasm.thm("int32_minus_one"),
                    @words.word_reduce_conv(tm("(word_not(word(0)) : \{w})")),
                  ] +
                  lift_rws(),
                ),
                @tactics.repeat_tac(@tactics.strip_tac),
                subst_vars(),
                arw([@arith.le_refl()]),
              ]),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let ors = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => (P : \{sassn})(vs,lc,gs,ms,h) || (R : \{sassn})(vs,lc,gs,ms,h)"

  let klift = (p : String) => {
    "keep((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),lift(\{p},(fr : \{hprop})),(store : Wstore),(frame : Wframe),(vs : List[Value]))"
  }
  let _ = lemma(
    "keep_lift_or",
    "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ fr : \{hprop}, ∀ store : Wstore, ∀ frame : Wframe, ∀ vs : List[Value], ∀ P : \{sassn}, ∀ R : \{sassn}, \{klift(ors)} == (\{klift("P")} || \{klift("R")})",
    seq([
      rw([thm("keep"), thm("lift"), thm("star_or"), @class.eta_ax()]),
      @meson.meson_tac(ths([])),
    ]),
  )
}
