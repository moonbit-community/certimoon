// The two branches that create a remainder, against word-level ownership.
// The callee specification is derived from the compiled all-bins push proof.

///|
fn prove_tlsf_split_paths() -> Unit raise {
  let w = w32
  let bt = "(Num) -> (Num) -> List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, x : String) => {
    "pts(val((\{a} : \{w})), serialise_i32((\{x} : \{w})))"
  }
  let at = (a : String, k : String) => "word_add((\{a} : \{w}), word(\{k}))"
  let star = (ps : Array[String]) => {
    let mut acc = "(fp : \{rty})((gs : List[Value]), (ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      acc = "star(\{ps[k]}, \{acc})"
    }
    acc
  }
  let pred = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => \{star(ps)}"
  }
  let z = i("word(0)")
  let size = "word_and((hd : \{w}), word(4294967292))"
  let r = "word_add((n : \{w}), word_add((m : \{w}), word(8)))"
  let next = "word_add(word_add((m : \{w}), \{size}), word(8))"
  let rem = "word_sub(word_sub(\{size}, (n : \{w})), word(8))"
  let rh0 = "word_and(word_or(\{rem}, word_and((w0 : \{w}), word(3))), word(4294967294))"
  let addr = "sfunc_ind((inst : Inst), (push : Num))"
  let zeros = "[\{z}, \{z}, \{z}]"
  let gspec = "tlsf_proved_spec(\{addr}, tlsf_push_code((d : \{w})), \{zeros}, 1, 1)"
  let falsep = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => F"
  let oldbins = "tlsf_bins((d : \{w}), (fl : \{w}), (sb : (Num) -> \{w}), (bl : \{bt}))"
  let newbins = "tlsf_bins((d : \{w}), tlsf_push_fl((\{rh0} : \{w}), (fl : \{w})), tlsf_push_sb((\{rh0} : \{w}), (sb : (Num) -> \{w})), tlsf_push_bl((\{rh0} : \{w}), (\{r} : \{w}), (bl : \{bt})))"
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t, List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ m : \{w}, ∀ n : \{w}, ∀ hd : \{w}, ∀ w0 : \{w}, ∀ w1 : \{w}, ∀ pf : \{w}, ∀ nf : \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  for last in [true, false] {
    let flag = if last { "!" } else { "" }
    let boundary = if last {
      "word_add(word_and(word_add((d : \{w}), word(15)), word(4294967280)), word(1908))"
    } else {
      at(next, "4")
    }
    let rf = if last {
      "word_or(word_and(\{rh0}, word(4294967293)), word(2))"
    } else {
      "word_and(\{rh0}, word(4294967293))"
    }
    let mh = if last {
      "word_and((hd : \{w}), word(4294967293))"
    } else {
      "(hd : \{w})"
    }
    let msized = "word_or((n : \{w}), word_and(\{mh}, word(3)))"
    let mf = "word_or(word_and(\{msized}, word(4294967294)), word(1))"
    let b = "wasm_bool(!(word_and((hd : \{w}), word(2)) == word(0)))"
    let ls0 = "[\{i("m")}, (l1 : Value), (l2 : Value), \{i("n")}, (l4 : Value), (l5 : Value)]"
    let ls1 = "[\{i("m")}, \{i(r)}, \{i(b)}, \{i("n")}, \{i(next)}, (l5 : Value)]"
    let p = pred([
      cell("m", "hd"),
      cell(r, "w0"),
      cell(at(r, "4"), "w1"),
      cell(at(r, "8"), "pf"),
      cell(at(r, "12"), "nf"),
      cell(boundary, "m"),
      oldbins,
    ])
    let q = pred([
      cell("m", mf),
      cell(r, rf),
      cell(at(r, "4"), "m"),
      cell(boundary, r),
      newbins,
    ])
    let q0 = pred([
      cell("m", msized),
      cell(r, rf),
      cell(at(r, "4"), "m"),
      cell(boundary, r),
      newbins,
    ])
    let q1 = pred([
      cell("m", "hd"),
      cell(r, rf),
      cell(at(r, "4"), "m"),
      cell(boundary, "m"),
      newbins,
    ])
    let q2 = pred([
      cell("m", mh),
      cell(r, rf),
      cell(at(r, "4"), "m"),
      cell(boundary, r),
      newbins,
    ])
    let fp_call = pred([
      cell("m", "hd"),
      cell(at(r, "4"), "m"),
      cell(boundary, "m"),
    ])
    let spec = inst(thm("tlsf_push_call"), [
      "(d : \{w})",
      addr,
      r,
      rh0,
      "(pf : \{w})",
      "(nf : \{w})",
      "(fl : \{w})",
      "(sb : (Num) -> \{w})",
      "(bl : \{bt})",
      fp_call,
    ])
    let cond = @basics.dest_imp(@kernel.concl(spec)).0
    let atoms = @basics.conjuncts(cond).to_array().map(@kernel.assume_rule)
    let spec = @bool.mp(spec, @bool.conj(atoms[0], atoms[1]))
    let spec = @simp.rewrite_rule(
      ths([thm("tlsf_push_pre"), thm("tlsf_push_post")]),
    )(spec)
    let hyp = "word_ugt(\{size}, word_add((n : \{w}), word(264))) && \{flag}(word_and((hd : \{w}), word(2)) == word(0)) && !(\{r} == word(0)) && 16 <= val(tlsf_size(\{rh0}))"
    let afters = [
      "st(NIL, \{ls1}, \{q0})",
      "st(NIL, \{ls1}, \{q1})",
      "st(NIL, \{ls1}, \{q2})",
    ]
    let name = if last { "tlsf_split_last_raw" } else { "tlsf_split_next_raw" }
    let stmt = "\{vars}, \{hyp} → sl_triple_g(\{gspec}, fs, tabs, inst, \{falsep}, st(NIL, \{ls0}, \{p}), tlsf_split_code(d, push), (vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => LENGTH(lc) == 6 && EL(0, lc) == \{i("m")} && EL(3, lc) == \{i("n")} && vs == NIL && (\{q})(gs, ms, h), NIL)"
    let rws = [
      @lists.el(),
      @lists.hd(),
      @lists.tl(),
      @lists.length(),
      thm("tlsf_size"),
      thm("tlsf_push_pre"),
      thm("tlsf_push_post"),
    ]
    let vc = seq([
      gen,
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      arw(rws + [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
    ])
    let _ = sym_prove(
      name,
      stmt,
      [],
      Array::make(3, vc),
      afters~,
      specs=[spec],
      calls=[(0, [])],
      rws~,
    )
  }
}
