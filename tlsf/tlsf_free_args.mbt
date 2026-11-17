///|
fn prove_tlsf_free_args() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let pred = (c : String) => {
    "(gs : List[Value]) => (ms : Num) => star(\{c},(fp : \{rty})(gs,ms))"
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
  let vars = "∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ m : \{w}, ∀ r : \{w}, ∀ hm : \{w}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let p = pred(cell("word_add((r : " + w + "),word(4))", "m"))
  let _ = sym_prove(
    "tlsf_free_prev_args_raw",
    "\{vars}, sl_triple(st(NIL,[\{i("r")},(l1 : Value),(l2 : Value)],\{p}),tlsf_free_prev_args(d,pop,push),st([\{i("m")}],[\{i("r")},\{i("m")},(l2 : Value)],\{p}))",
    [],
    () => [vc],
  )
  let r0 = "word_add(word_add((m : \{w}),word_and((hm : \{w}),word(4294967292))),word(8))"
  let q = pred(cell("m", "hm"))
  let _ = sym_prove(
    "tlsf_free_next_args_raw",
    "\{vars}, sl_triple(st(NIL,[\{i("m")},(l1 : Value),(l2 : Value)],\{q}),tlsf_free_next_args(d,pop,push),st([\{i(r0)}],[\{i("m")},\{i(r0)},(l2 : Value)],\{q}))",
    [],
    () => [vc],
  )
}
