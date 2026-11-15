// Restore the complete invariant after the compiled split-and-mark suffix.
// The _all specs accept one whole free payload, with arbitrary byte contents.
// Existing client bytes are carried in the same arbitrary fp before and after.

///|
fn prove_tlsf_split_all() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let h = "(hd : \{ht})((m : \{w}))"
  let r = "tlsf_remainder((m : \{w}), (n : \{w}))"
  let rs = "tlsf_remainder_size(\{h}, (n : \{w}))"
  let nh = "tlsf_split_headers((hd : \{ht}), (m : \{w}), (n : \{w}))"
  let marked = "tlsf_mark((hd : \{ht}), (m : \{w}))"
  let next = "word_add(word_add((m : \{w}), tlsf_size(\{h})), word(8))"
  let seed = "word_and(word_or(\{rs}, word_and((w0 : \{w}), word(3))), word(4294967294))"
  let star = (ps : Array[String]) => {
    let mut s = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      s = "star(\{ps[k]}, \{s})"
    }
    s
  }
  let addr = "sfunc_ind((inst : Inst), (push : Num))"
  let native = "EL(\{addr}, (fs : List[Cl])) == Func_native((inst : Inst), Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code((d : \{w})))"
  let nfl = "tlsf_push_fl(\{rs}, (fl : \{w}))"
  let nsb = "tlsf_push_sb(\{rs}, (sb : (Num) -> \{w}))"
  let nbl = "tlsf_push_bl(\{rs}, \{r}, (bl : \{bt}))"
  let payload = "tlsf_bytes(val((m : \{w})) + 8, val((n : \{w})))"
  let ac = [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]
  let rdef = @simp.rewrite_conv(ths([thm("tlsf_remainder")]))(tm(r))
  let rsdef = @simp.rewrite_conv(ths([thm("tlsf_remainder_size")]))(tm(rs))
  let normal = [
    @equal.gsym(thm("tlsf_size")),
    @equal.gsym(rdef),
    @equal.gsym(rsdef),
  ]
  for last in [true, false] {
    let zs = if last {
      "(NIL : \{lw})"
    } else {
      "CONS((\{next} : \{w}), (zs : \{lw}))"
    }
    let top = if last { "(m : \{w})" } else { "(top : \{w})" }
    let newtop = if last { r } else { top }
    let oldxs = "APPEND((ys : \{lw}), CONS((m : \{w}), \{zs}))"
    let newxs = "APPEND((ys : \{lw}), CONS((m : \{w}), CONS(\{r}, \{zs})))"
    let args = [
      "(ys : \{lw})",
      zs,
      "(m : \{w})",
      "(n : \{w})",
      "(d : \{w})",
      "(lim : Num)",
      top,
      "(hd : \{ht})",
    ]
    let common = "tlsf_physical_ok((d : \{w}), (lim : Num), \{top}, \{oldxs}, (hd : \{ht})) && !tlsf_used(\{h}) && 16 <= val((n : \{w})) && val(n) <= 4160749568 && MOD(val(n), 16) == 0 && val(n) + 264 < val(tlsf_size(\{h}))"
    let cond = "\{native} && \{common} && tlsf_bins_match(\{oldxs}, \{marked}, (bl : \{bt})) && \{if last { "!" } else { "" }}(word_and(\{h}, word(2)) == word(0))"
    let mut rest = [
      "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))",
      cell(
        "word_add((m : " + w + "), word(4))",
        "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
      ),
      payload,
      "tlsf_bytes(val(\{r}) + 16, val(\{rs}) - 8)",
    ]
    if !last {
      rest = rest +
        [
          cell("word_add(tlsf_base((d : " + w + ")), word(1908))", top),
          cell(next, "(hd : " + ht + ")(" + next + ")"),
          "tlsf_spare((\{next} : \{w}), (hd : \{ht})(\{next}))",
          "tlsf_regions((\{next} : \{w}), (zs : \{lw}), (hd : \{ht}))",
        ]
    }
    let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(rest)}(h)"
    let rawname = if last {
      "tlsf_split_last_raw"
    } else {
      "tlsf_split_next_raw"
    }
    let raw = inst(thm(rawname), [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t, List[V_ref])])",
      "(inst : Inst)",
      "(d : \{w})",
      "(push : Num)",
      "(m : \{w})",
      "(n : \{w})",
      h,
      "(w0 : \{w})",
      "(w1 : \{w})",
      "(pf : \{w})",
      "(nf : \{w})",
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      "(l1 : Value)",
      "(l2 : Value)",
      "(l4 : Value)",
      "(l5 : Value)",
      frame,
    ])
    let path = @simp.rewrite_rule(ths(normal))(raw)
    let p = args_of(@basics.dest_imp(@kernel.concl(path)).1, "sl_triple_g", 9).unwrap()[5]
    let large = "tlsf_large((d : \{w}), (lim : Num), \{newtop}, \{newxs}, \{nh}, \{nfl}, \{nsb}, \{nbl})"
    let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == V_num(ConstInt32((m : \{w}))) && EL(3, lc) == V_num(ConstInt32((n : \{w}))) && vs == NIL && ms == (lim : Num) && star(\{large}, star(\{payload}, (fp : \{rty})(gs, ms)), h)"
    let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ ys : \{lw}, ∀ zs : \{lw}, ∀ m : \{w}, ∀ n : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ w0 : \{w}, ∀ w1 : \{w}, ∀ pf : \{w}, ∀ nf : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
    let close = inst(
      thm("tlsf_split_close"),
      args +
      [
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "(fp : \{rty})((gs : List[Value]), (ms : Num))",
      ],
    )
    let post = seq([
      gen,
      beta_goal(),
      rw(lift_rws()),
      strip,
      @tactics.mp_tac(
        @simp.rewrite_rule(
          ths([thm("tlsf_regions"), @lists.not_cons_nil()] + lift_rws() + ac),
        )(close),
      ),
      arw([@lists.not_cons_nil()]),
      @tactics.disch_then(th => {
        @tactics.mp_tac(@equal.ap_thm(th, tm("(h : \{heap})")))
      }),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(
        [
          thm("tlsf_split_taken_last"),
          thm("tlsf_split_taken_next"),
          thm("tlsf_remainder_seed_clear"),
          thm("tlsf_regions"),
          thm("tlsf_base"),
          @words.word_or_0(),
          @lists.not_cons_nil(),
        ] +
        lift_rws() +
        ac,
      ),
      @meson.meson_tac(ths([])),
    ])
    let tactic = seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_split_focus_geometry"), args)),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_split_focus"), args)),
      arw([]),
      strip,
      @tactics.rule_assum_tac(@simp.rewrite_rule(ths([@lists.not_cons_nil()]))),
      @tactics.mp_tac(
        inst(thm("tlsf_split_bins_focus"), [
          "(ys : \{lw})",
          zs,
          "(m : \{w})",
          "(n : \{w})",
          "(hd : \{ht})",
          "(bl : \{bt})",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      have(
        "tlsf_size(\{seed}) == \{rs}",
        seq([@tactics.match_mp_tac(thm("tlsf_remainder_seed_size")), arw([])]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_push_size_cong"), [
          seed,
          rs,
          r,
          "(fl : \{w})",
          "(sb : (Num) -> \{w})",
          "(bl : \{bt})",
        ]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_split_test"), [h, "(n : \{w})"])),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(inst(thm("tlsf_last_mask_cases"), [h])),
      arw([]),
      @tactics.try_tac(@tactics.disch_tac),
      @tactics.mp_tac(
        inst(
          thm(
            if last {
              "tlsf_split_taken_last"
            } else {
              "tlsf_split_taken_next"
            },
          ),
          ["(n : \{w})", h],
        ),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_remainder_seed_clear"), [rs, "(w0 : \{w})"]),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("tlsf_split_in_module")),
      arw([]),
      tlsf_split_conseq(path, ent_tac([], []), post),
    ])
    let focused = lemma(
      if last {
        "tlsf_split_last"
      } else {
        "tlsf_split_next"
      },
      "\{vars}, \{cond} → sl_triple_m(fs, tabs, inst, \{show(p)}, tlsf_split_code(d, push), \{q}, NIL)",
      tactic,
    )
    // Recover the ordinary whole-payload post-pop state. Its four new
    // metadata words have arbitrary contents, discharged with sl_ex_m.
    let states = [
      "(vs : List[Value])",
      "(lc : List[Value])",
      "(gs : List[Value])",
      "(ms : Num)",
      "(h : " + heap + ")",
    ]
    let mut exbody = @basics.list_mk_comb(p, @list.List(states.map(tm)))
    let ghosts = [
      "(w0 : " + w + ")",
      "(w1 : " + w + ")",
      "(pf : " + w + ")",
      "(nf : " + w + ")",
    ]
    for k = ghosts.length() - 1; k >= 0; k = k - 1 {
      exbody = @bool.mk_exists(tm(ghosts[k]), exbody)
    }
    let mut expre = exbody
    for k = states.length() - 1; k >= 0; k = k - 1 {
      expre = @kernel.mk_abs(tm(states[k]), expre)
    }
    let topcell = cell("word_add(tlsf_base((d : " + w + ")), word(1908))", top)
    let mut wholeparts = [
      cell("m", h),
      topcell,
      "tlsf_regions((word(0) : \{w}), (ys : \{lw}), (hd : \{ht}))",
      cell(
        "word_add((m : " + w + "), word(4))",
        "tlsf_end((word(0) : " + w + "), (ys : " + lw + "))",
      ),
      "tlsf_bytes(val((m : \{w})) + 8, val(tlsf_size(\{h})))",
    ]
    if !last {
      wholeparts = wholeparts +
        ["tlsf_regions((m : \{w}), \{zs}, (hd : \{ht}))"]
    }
    wholeparts = wholeparts +
      ["tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"]
    let initiallocals = args_of(p, "st", 3).unwrap()[1]
    let natural = "st((NIL : List[Value]), \{show(initiallocals)}, (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && \{star(wholeparts)}(h))"
    let a = "val((m : \{w})) + 8"
    let cut = inst(thm("tlsf_split_payload_cut"), [
      a,
      "val((n : \{w}))",
      "val(\{rs})",
      "val(tlsf_size(\{h}))",
    ])
    let eqcut = @basics.dest_imp(@kernel.concl(cut)).1
    let pre_ent = seq([
      have(
        show(eqcut),
        seq([@tactics.match_mp_tac(cut), arw([]), @int.asm_arith_tac]),
      ),
      gen,
      rw([thm("st")] + lift_rws()),
      beta_goal(),
      arw(
        [
          thm("tlsf_bytes_four_words"),
          thm("tlsf_regions"),
          thm("tlsf_base"),
          @lists.not_cons_nil(),
        ] +
        lift_rws() +
        ac,
      ),
    ])
    let core = seq(
      ghosts.map(x => {
        seq([
          @tactics.match_mp_tac(thm("sl_ex_m")),
          beta_goal(),
          @tactics.x_gen_tac(tm(x)),
        ])
      }) +
      [rw([@class.eta_ax()]), @tactics.match_mp_tac(focused), arw([])],
    )
    let allvars = vars.replace(
      old="∀ w0 : \{w}, ∀ w1 : \{w}, ∀ pf : \{w}, ∀ nf : \{w}, ",
      new="",
    )
    let _ = lemma(
      if last {
        "tlsf_split_last_all"
      } else {
        "tlsf_split_next_all"
      },
      "\{allvars}, \{cond} → sl_triple_m(fs, tabs, inst, \{natural}, tlsf_split_code(d, push), \{q}, NIL)",
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_split_focus_geometry"), args)),
        arw([]),
        strip,
        have(
          "tlsf_block_ok(val((m : \{w})), (lim : Num), m, (hd : \{ht})) && (lim : Num) <= 4294967296",
          seq([
            @tactics.undisch_tac(
              tm(
                "tlsf_physical_ok((d : \{w}), (lim : Num), \{top}, \{oldxs}, (hd : \{ht}))",
              ),
            ),
            rw([thm("tlsf_physical_ok")]),
            strip,
            arw([]),
            @tactics.match_mp_tac(
              inst(thm("tlsf_layout_members"), [
                oldxs,
                "(word(0) : \{w})",
                "tlsf_origin((d : \{w}))",
                "(lim : Num)",
                top,
                "(hd : \{ht})",
                "(m : \{w})",
              ]),
            ),
            arw([@lists.mem_append(), @lists.mem()]),
          ]),
        ),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "/\\" {
            @tactics.strip_assume_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "tlsf_block_ok" {
            @tactics.strip_assume_tac(
              @simp.rewrite_rule(ths([thm("tlsf_block_ok")]))(th),
            )
          } else {
            @tactics.no_tac
          }
        }),
        seq(
          [4, 8, 12].map(k => {
            have(
              "val(word_add(\{r}, word(\{k}))) == val(\{r}) + \{k}",
              seq([
                @tactics.match_mp_tac(thm("val_add_small")),
                @int.asm_arith_tac,
              ]),
            )
          }),
        ),
        @tactics.match_mp_tac(thm("sl_conseq_m")),
        @tactics.exists_tac(expre),
        @tactics.exists_tac(tm(q)),
        @simp.rewrite_tac(ths([])),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([solve(core), solve(pre_ent), solve(same_tac())]),
        ),
      ]),
    )
  }
}
