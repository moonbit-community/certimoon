///|
fn prove_tlsf_ensure_geometry() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_physical_last",
    "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, tlsf_physical_ok(d,lim,top,xs,hd) → (∃ ys : \{lw}, xs == APPEND(ys,[top]))",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.assume_tac(inst(thm("snoc_cases"), ["(xs : \{lw})"])),
      @meson.asm_meson_tac(
        ths([thm("tlsf_focus_last"), thm("tlsf_physical_ok")]),
      ),
    ]),
  )
  let next = "(a : Num) + 8 + val(tlsf_size((hd : \{ht})((h : \{w}))))"
  let _ = lemma(
    "tlsf_path_limit",
    "∀ ys : \{lw}, ∀ a : Num, ∀ oldlim : Num, ∀ newlim : Num, ∀ hd : \{ht}, ∀ b : Num, tlsf_path(ys,a,oldlim,hd,b) && oldlim <= newlim → tlsf_path(ys,a,newlim,hd,b)",
    seq([
      @lists.list_induct_tac,
      rw([thm("tlsf_path")]),
      gen,
      strip,
      @tactics.first(
        @list.List([
          solve(arw([])),
          seq([
            @tactics.conj_tac,
            @tactics.first(
              @list.List([
                solve(
                  seq([
                    @tactics.undisch_tac(
                      tm(
                        "tlsf_block_ok((a : Num),(oldlim : Num),(h : \{w}),(hd : \{ht}))",
                      ),
                    ),
                    rw([thm("tlsf_block_ok")]),
                    strip,
                    arw([thm("tlsf_block_ok")]),
                    @int.asm_arith_tac,
                  ]),
                ),
                solve(
                  seq([
                    @tactics.conj_tac,
                    arw([]),
                    @tactics.first_x_assum(th => {
                      @tactics.match_mp_tac(
                        inst(th, [
                          next,
                          "(oldlim : Num)",
                          "(newlim : Num)",
                          "(hd : \{ht})",
                          "(b : Num)",
                        ]),
                      )
                    }),
                    arw([]),
                  ]),
                ),
              ]),
            ),
          ]),
        ]),
      ),
    ]),
  )
  let xs = "APPEND((ys : \{lw}),[(m : \{w})])"
  let pref = "tlsf_path((ys : \{lw}),(a : Num),(newlim : Num),(hd : \{ht}),val((m : \{w})))"
  let agree = "∀ x : \{w}, MEM(x,(ys : \{lw})) → (hd : \{ht})(x) == (nh : \{ht})(x)"
  let vars = "∀ ys : \{lw}, ∀ p : \{w}, ∀ a : Num, ∀ oldlim : Num, ∀ newlim : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}"
  let old = "tlsf_layout((p : \{w}),(a : Num),(oldlim : Num),(m : \{w}),\{xs},(hd : \{ht}))"
  let cut = inst(thm("tlsf_layout_cut_at"), [
    "(ys : \{lw})",
    "(NIL : \{lw})",
    "(m : \{w})",
    "(p : \{w})",
    "(a : Num)",
    "(oldlim : Num)",
    "(m : \{w})",
    "(hd : \{ht})",
  ])
  let unfold_old = seq([
    @tactics.mp_tac(cut),
    arw([]),
    strip,
    @tactics.undisch_tac(
      tm(
        "tlsf_layout(tlsf_end((p : \{w}),(ys : \{lw})),val((m : \{w})),(oldlim : Num),m,[(m : \{w})],(hd : \{ht}))",
      ),
    ),
    rw([thm("tlsf_layout"), thm("tlsf_block_ok")]),
    strip,
    have(
      pref,
      seq([
        @tactics.match_mp_tac(
          inst(thm("tlsf_path_limit"), [
            "(ys : \{lw})",
            "(a : Num)",
            "(oldlim : Num)",
            "(newlim : Num)",
            "(hd : \{ht})",
            "val((m : \{w}))",
          ]),
        ),
        arw([]),
      ]),
    ),
  ])
  let fields = "16 <= val(tlsf_size((nh : \{ht})((m : \{w})))) && MOD(val(tlsf_size(nh(m))),8) == 0 && val(m) + 8 + val(tlsf_size(nh(m))) == (newlim : Num) && tlsf_last(nh(m))"
  let _ = lemma(
    "tlsf_layout_extend_last",
    "\{vars}, \{old} && oldlim <= newlim && (\{agree}) && \{fields} → tlsf_layout(p,a,newlim,m,\{xs},nh)",
    seq([
      gen,
      strip,
      unfold_old,
      @tactics.match_mp_tac(
        inst(thm("tlsf_layout_glue"), [
          "(ys : \{lw})",
          "(NIL : \{lw})",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "val((m : \{w}))",
          "(newlim : Num)",
          "(m : \{w})",
          "(hd : \{ht})",
          "(nh : \{ht})",
        ]),
      ),
      arw([thm("tlsf_layout"), thm("tlsf_block_ok"), @arith.le_refl()]),
    ]),
  )
  let nr = "val(tlsf_size((nh : \{ht})((r : \{w}))))"
  let more = "tlsf_size((nh : \{ht})((m : \{w}))) == tlsf_size((hd : \{ht})(m)) && !tlsf_last(nh(m)) && tlsf_last(nh((r : \{w}))) && val(r) == (oldlim : Num) && MOD(val(r),8) == 0 && 16 <= \{nr} && MOD(\{nr},8) == 0 && val(r) + 8 + \{nr} == (newlim : Num)"
  let _ = lemma(
    "tlsf_layout_append_last",
    "\{vars}, ∀ r : \{w}, \{old} && oldlim <= newlim && (\{agree}) && \{more} → tlsf_layout(p,a,newlim,r,APPEND(ys,[m,r]),nh)",
    seq([
      gen,
      strip,
      unfold_old,
      have("MOD((oldlim : Num),8) == 0", @meson.asm_meson_tac(ths([]))),
      have(
        "!((r : \{w}) == word(0))",
        seq([rw([@equal.gsym(@words.val_eq_0())]), @int.asm_arith_tac]),
      ),
      @tactics.match_mp_tac(
        inst(thm("tlsf_layout_glue"), [
          "(ys : \{lw})",
          "[(r : \{w})]",
          "(m : \{w})",
          "(p : \{w})",
          "(a : Num)",
          "val((m : \{w}))",
          "(newlim : Num)",
          "(r : \{w})",
          "(hd : \{ht})",
          "(nh : \{ht})",
        ]),
      ),
      arw([
        thm("tlsf_layout"),
        thm("tlsf_block_ok"),
        @arith.le_refl(),
        @lists.not_cons_nil(),
      ]),
      @int.asm_arith_tac,
    ]),
  )
  let physvars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ oldlim : Num, ∀ newlim : Num, ∀ m : \{w}, ∀ hd : \{ht}, ∀ nh : \{ht}"
  let physical = "tlsf_physical_ok((d : \{w}),(oldlim : Num),(m : \{w}),\{xs},(hd : \{ht}))"
  let newbounds = "(newlim : Num) <= 4294967296 && MOD(newlim,65536) == 0"
  let ground = @meson.asm_meson_tac(ths([]))
  let mono = seq([
    @tactics.match_mp_tac(
      inst(thm("tlsf_coalesced_mono"), [xs, "(hd : \{ht})", "(nh : \{ht})"]),
    ),
    arw([]),
    @tactics.x_gen_tac(tm("(x : \{w})")),
    rw([@lists.mem_append(), @lists.mem()]),
    strip,
    @tactics.first_x_assum(th => {
      if @basics.is_forall(@kernel.concl(th)) {
        @tactics.assume_tac(@bool.spec(tm("(x : \{w})"), th))
      } else {
        @tactics.no_tac
      }
    }),
    ground,
  ])
  let _ = lemma(
    "tlsf_physical_extend_last",
    "\{physvars}, \{physical} && !tlsf_used(hd(m)) && oldlim <= newlim && \{newbounds} && (\{agree}) && \{fields} → tlsf_physical_ok(d,newlim,m,\{xs},nh)",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      have(
        "tlsf_layout((word(0) : \{w}),tlsf_origin((d : \{w})),(newlim : Num),(m : \{w}),\{xs},(nh : \{ht}))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_extend_last"), [
              "(ys : \{lw})",
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(oldlim : Num)",
              "(newlim : Num)",
              "(m : \{w})",
              "(hd : \{ht})",
              "(nh : \{ht})",
            ]),
          ),
          arw([]),
        ]),
      ),
      arw([@lists.append_eq_nil(), @lists.not_cons_nil()]),
      mono,
    ]),
  )
  let _ = lemma(
    "tlsf_physical_append_last",
    "\{physvars}, ∀ r : \{w}, \{physical} && tlsf_used(nh(m)) && oldlim <= newlim && \{newbounds} && (\{agree}) && \{more} → tlsf_physical_ok(d,newlim,r,APPEND(ys,[m,r]),nh)",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      have(
        "tlsf_layout((word(0) : \{w}),tlsf_origin((d : \{w})),(newlim : Num),(r : \{w}),APPEND((ys : \{lw}),[(m : \{w}),r]),(nh : \{ht}))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_layout_append_last"), [
              "(ys : \{lw})",
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(oldlim : Num)",
              "(newlim : Num)",
              "(m : \{w})",
              "(hd : \{ht})",
              "(nh : \{ht})",
              "(r : \{w})",
            ]),
          ),
          arw([]),
        ]),
      ),
      have("tlsf_coalesced(\{xs},(nh : \{ht}))", mono),
      arw([@lists.append_eq_nil(), @lists.not_cons_nil()]),
      @tactics.match_mp_tac(
        inst(thm("tlsf_coalesced_splice"), [
          "(ys : \{lw})",
          "(m : \{w})",
          "(r : \{w})",
          "(NIL : \{lw})",
          "(nh : \{ht})",
        ]),
      ),
      arw([]),
    ]),
  )
}
