// The three split-and-mark paths behind one allocator ownership boundary.
// All returned payload bytes are separated from both metadata and clients.

///|
fn prove_tlsf_split_detached() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let n = "(n : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let r = "tlsf_remainder(\{m}, \{n})"
  let rs = "tlsf_remainder_size(\{h}, \{n})"
  let nh = "tlsf_split_headers(\{hd}, \{m}, \{n})"
  let marked = "tlsf_mark(\{hd}, \{m})"
  let next = "word_add(word_add(\{m}, tlsf_size(\{h})), word(8))"
  let oldxs = "APPEND((ys : \{lw}), CONS(\{m}, (zs : \{lw})))"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
  let p = "st(NIL, \{lc}, (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(tlsf_detached((d : \{w}), lim, (top : \{w}), (ys : \{lw}), \{m}, (zs : \{lw}), \{hd}, (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt})), (fp : \{rty})(gs, ms), h))"
  let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == \{i("m")} && EL(3, lc) == \{i("n")} && vs == NIL && ms == (lim : Num) && tlsf_allocated((d : \{w}), lim, \{m}, \{n}, \{oldxs}, \{hd}, (fp : \{rty})(gs, ms), h)"
  let native = "EL(sfunc_ind((inst : Inst), (push : Num)), (fs : List[Cl])) == Func_native(inst, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let cond = "\{native} && tlsf_physical_ok((d : \{w}), (lim : Num), (top : \{w}), \{oldxs}, \{hd}) && !tlsf_used(\{h}) && tlsf_bins_match(\{oldxs}, \{marked}, (bl : \{bt})) && 16 <= val(\{n}) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) <= val(tlsf_size(\{h}))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let close = (path : @kernel.Thm, post : @tactics.Tactic) => {
    let ts = args_of(@basics.dest_imp(@kernel.concl(path)).1, "sl_triple_m", 7).unwrap()
    seq([
      @tactics.match_mp_tac(thm("sl_conseq_m")),
      @tactics.exists_tac(ts[3]),
      @tactics.exists_tac(ts[5]),
      @simp.rewrite_tac(ths([])),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(seq([@tactics.match_mp_tac(path), arw([]), @int.asm_arith_tac])),
          solve(seq([ent_tac([thm("tlsf_detached"), thm("tlsf_regions")], [])])),
          solve(post),
        ]),
      ),
    ])
  }
  let args = (zs : String, top : String) => {
    [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t, List[V_ref])])",
      "(inst : Inst)",
      "(d : \{w})",
      "(push : Num)",
      "(ys : \{lw})",
      zs,
      m,
      n,
      "(lim : Num)",
      top,
      hd,
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(l1 : Value)",
      "(l2 : Value)",
      "(l4 : Value)",
      "(l5 : Value)",
      "(fp : \{rty})",
    ]
  }
  let marksize = "tlsf_size((\{marked})(\{m})) == tlsf_size(\{h})"
  let markused = "tlsf_used((\{marked})(\{m}))"
  let nosplit = seq([
    free_have(
      "tlsf_retains(\{oldxs},\{hd},\{oldxs},\{marked})",
      seq([@tactics.match_mp_tac(thm("tlsf_retains_mark")), arw([])]),
    ),
    close(
      inst(thm("tlsf_split_whole"), args("(zs : \{lw})", "(top : \{w})")),
      ent_tac(
        [
          thm("tlsf_allocated"),
          @arith.le_refl(),
          @kernel.assume_rule(tm(marksize)),
          @kernel.assume_rule(tm(markused)),
          @lists.mem_append(),
          @lists.mem(),
        ],
        [
          "(top : \{w})",
          oldxs,
          marked,
          "(fl : \{w})",
          "(sb : (Num) -> \{w})",
          "(bl : \{bt})",
        ],
      ),
    ),
  ])
  let splitcase = (last : Bool) => {
    let suffix = if last {
      "(NIL : \{lw})"
    } else {
      "CONS(\{next}, (t : \{lw}))"
    }
    let top = if last { m } else { "(top : \{w})" }
    let newxs = "APPEND((ys : \{lw}), CONS(\{m}, CONS(\{r}, \{suffix})))"
    let nhsize = "tlsf_size((\{nh})(\{m})) == \{n}"
    let nhused = "tlsf_used((\{nh})(\{m}))"
    let ws = [
      if last {
        r
      } else {
        top
      },
      newxs,
      nh,
      "tlsf_push_fl(\{rs}, (fl : \{w}))",
      "tlsf_push_sb(\{rs}, (sb : (Num) -> \{w}))",
      "tlsf_push_bl(\{rs}, \{r}, (bl : \{bt}))",
    ]
    let models = [
      "(ys : \{lw})",
      suffix,
      m,
      n,
      "(d : \{w})",
      "(lim : Num)",
      top,
      hd,
    ]
    let path = inst(
      thm(if last { "tlsf_split_last_all" } else { "tlsf_split_next_all" }),
      args(if last { "(NIL : \{lw})" } else { "(t : \{lw})" }, top),
    )
    seq([
      @tactics.mp_tac(inst(thm("tlsf_split_focus_geometry"), models)),
      arw([]),
      strip,
      have("!(\{m} == \{r})", @meson.asm_meson_tac(ths([]))),
      have(
        "(\{nh})(\{m}) == word_or(\{n}, word(1))",
        seq([rw([thm("tlsf_split_headers"), thm("tlsf_put")]), arw([])]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_taken_fields"), [n])),
      arw([]),
      strip,
      have(nhsize, arw([])),
      have(nhused, arw([])),
      free_have(
        "tlsf_retains(APPEND((ys : \{lw}),CONS(\{m},\{suffix})),\{hd},\{newxs},\{nh})",
        seq([@tactics.match_mp_tac(thm("tlsf_retains_split")), arw([])]),
      ),
      close(
        path,
        seq([
          ent_tac(
            [
              thm("tlsf_allocated"),
              @arith.le_refl(),
              @kernel.assume_rule(tm(nhsize)),
              @kernel.assume_rule(tm(nhused)),
              @lists.mem_append(),
              @lists.mem(),
            ],
            ws,
          ),
        ]),
      ),
    ])
  }
  let eqtop = @kernel.assume_rule(tm("(top : \{w}) == \{m}"))
  let eqnext = @kernel.assume_rule(tm("(h : \{w}) == \{next}"))
  let _ = lemma(
    "tlsf_split_detached",
    "\{vars}, \{cond} → sl_triple_m(fs, tabs, inst, \{p}, tlsf_split_code(d, push), \{q}, NIL)",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(
          inst(thm("tlsf_focus_block"), [
            "(ys : \{lw})",
            "(zs : \{lw})",
            m,
            "(d : \{w})",
            "(lim : Num)",
            "(top : \{w})",
            hd,
          ]),
        ),
        arw([]),
        strip,
        have(
          "!(\{m} == word(0))",
          seq([
            @tactics.undisch_tac(
              tm("tlsf_block_ok(val(\{m}), (lim : Num), \{m}, \{hd})"),
            ),
            rw([thm("tlsf_block_ok")]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        have(
          marksize,
          seq([
            rw([thm("tlsf_mark"), thm("tlsf_put")]),
            @tactics.mp_tac(inst(thm("tlsf_used_store_fields"), [h])),
            @meson.meson_tac(ths([])),
          ]),
        ),
        have(
          markused,
          @tactics.accept_tac(inst(thm("tlsf_mark_used"), [hd, m])),
        ),
        @tactics.thenl(
          @class.asm_cases_tac(
            tm("word_ugt(tlsf_size(\{h}), word_add(\{n}, word(264)))"),
          ),
          @list.List([
            seq([
              @tactics.mp_tac(inst(thm("tlsf_split_test"), [h, n])),
              arw([]),
              @tactics.disch_tac,
              @tactics.thenl(
                seq([
                  @tactics.strip_assume_tac(
                    inst(@lists.list_cases(), ["(zs : \{lw})"]),
                  ),
                  subst_vars(),
                ]),
                @list.List([
                  seq([
                    @tactics.mp_tac(
                      inst(thm("tlsf_focus_last"), [
                        "(ys : \{lw})",
                        m,
                        "(d : \{w})",
                        "(lim : Num)",
                        "(top : \{w})",
                        hd,
                      ]),
                    ),
                    arw([]),
                    strip,
                    @tactics.subst1_tac(eqtop),
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(ths([eqtop, thm("tlsf_last")])),
                    ),
                    splitcase(true),
                  ]),
                  seq([
                    @tactics.mp_tac(
                      inst(thm("tlsf_focus_next"), [
                        "(ys : \{lw})",
                        "(t : \{lw})",
                        m,
                        "(h : \{w})",
                        "(d : \{w})",
                        "(lim : Num)",
                        "(top : \{w})",
                        hd,
                      ]),
                    ),
                    arw([]),
                    strip,
                    @tactics.subst1_tac(eqnext),
                    @tactics.rule_assum_tac(
                      @simp.rewrite_rule(ths([eqnext, thm("tlsf_last")])),
                    ),
                    splitcase(false),
                  ]),
                ]),
              ),
            ]),
            nosplit,
          ]),
        ),
      ])
    },
  )
}
