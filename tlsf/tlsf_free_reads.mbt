// The mark-free store and the two short-circuit neighbour tests, on owned
// header words. In particular a missing neighbour is never dereferenced.

///|
fn prove_tlsf_free_reads() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (ps : Array[String]) => {
    let mut out = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
    for k = ps.length() - 1; k >= 0; k = k - 1 {
      out = "star(\{ps[k]},\{out})"
    }
    "(gs : List[Value]) => (ms : Num) => \{out}"
  }
  let vc = seq([
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.asm_rewrite_tac(
      ths([thm("star_assoc"), thm("star_comm"), thm("star_left_comm")]),
    ),
  ])
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ h : \{w}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let lc = "[\{i("m")},(l1 : Value),(l2 : Value)]"
  let _ = sym_prove(
    "tlsf_free_clear_raw",
    "\{vars}, sl_triple(st(NIL,\{lc},\{pred([cell("m","h")])}),tlsf_free_clear(d,pop,push),st(NIL,\{lc},\{pred([cell("m","word_and((h : "+w+"),word(4294967294))")])}))",
    [],
    () => [vc],
  )
  for zero in [true, false] {
    let p = if zero { "(word(0) : \{w})" } else { "(p : \{w})" }
    let ps = [cell("word_add((m : " + w + "),word(4))", p)]
    if !zero {
      ps.push(cell(p, "h"))
    }
    let r = pred(ps)
    let lc1 = "[\{i("m")},\{i("word_add((m : "+w+"),word(4))")},(l2 : Value)]"
    let flag = if zero {
      "(word(1) : \{w})"
    } else {
      "word_and((h : \{w}),word(1))"
    }
    let cond = if zero { "T" } else { "!((p : \{w}) == word(0))" }
    let _ = sym_prove(
      if zero {
        "tlsf_free_prev_zero_raw"
      } else {
        "tlsf_free_prev_nonzero_raw"
      },
      "\{vars}, ∀ p : \{w}, \{cond} → sl_triple(st(NIL,\{lc},\{r}),tlsf_free_prev_test(d,pop,push),st([\{i("wasm_bool(\{flag} == word(0))")}],\{lc1},\{r}))",
      [],
      () => if zero { [vc, vc] } else { [vc] },
      afters=["st([\{i(flag)}],\{lc1},\{r})"],
    )
  }
  for last in [true, false] {
    let nx = "word_add(word_add((m : \{w}),word_and((h : \{w}),word(4294967292))),word(8))"
    let ps = [cell("m", "h")]
    if !last {
      ps.push(cell(nx, "nh"))
    }
    let r = pred(ps)
    let flag = if last {
      "(word(1) : \{w})"
    } else {
      "word_and((nh : \{w}),word(1))"
    }
    let cond = if last {
      "!(word_and((h : \{w}),word(2)) == word(0))"
    } else {
      "word_and((h : \{w}),word(2)) == word(0)"
    }
    let _ = sym_prove(
      if last {
        "tlsf_free_next_last_raw"
      } else {
        "tlsf_free_next_nonlast_raw"
      },
      "\{vars}, ∀ nh : \{w}, \{cond} → sl_triple(st(NIL,\{lc},\{r}),tlsf_free_next_test(d,pop,push),st([\{i("wasm_bool(\{flag} == word(0))")}],\{lc},\{r}))",
      [],
      () => if last { [vc, vc] } else { [vc] },
      afters=["st([\{i(flag)}],\{lc},\{r})"],
      rws=[thm("tlsf_size"), thm("tlsf_last")],
    )
  }
}
