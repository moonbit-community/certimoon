// A single exposed slot between the initialized prefix and the raw suffix.

///|
fn define_tlsf_page_allocate_work() -> Unit raise {
  let w = w32
  let p = "(p : \{w})"
  let s = "(s : Num)"
  let k = "(k : Num)"
  let b = "tlsf_small_slot(\{p},\{s},\{k})"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let ps = [
    cell("val(p)+8", "word(s)"),
    cell("val(p)+12", "word(tlsf_small_total(s))"),
    cell("val(p)+16", "used0"),
    cell("val(p)+20", "head"),
    cell("val(p)+24", "prev0"),
    cell("val(p)+28", "word(0)"),
    "tlsf_istar(tlsf_page_allocate_slot(p,s),k)",
    cell("val(" + b + ")", "w0"),
    cell("val(" + b + ")+4", "w1"),
    cell("val(" + b + ")+8", "w2"),
    "tlsf_bytes(val(\{b})+12,s-4)",
    "tlsf_bytes(val(p)+32+(8+s)*SUC(k),(cap : Num)-24-(8+s)*SUC(k))",
  ]
  def(
    "tlsf_page_allocate_work",
    "tlsf_page_allocate_work(\{p},(cap : Num),\{s},\{k},(used0 : \{w}),(prev0 : \{w}),(head : \{w}),(w0 : \{w}),(w1 : \{w}),(w2 : \{w})) == \{small_star(ps)}",
  )
}

///|
fn prove_tlsf_page_allocate_work() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let p = "(p : \{w})"
  let s = "(s : Num)"
  let cap = "(cap : Num)"
  let k = "(k : Num)"
  let b = "tlsf_small_slot(\{p},\{s},\{k})"
  let a = "val(\{p})+32+(8+\{s})*\{k}"
  let n = "\{cap}-24-(8+\{s})*\{k}"
  let rem = "\{cap}-24-(8+\{s})*SUC(\{k})"
  let geom = "tlsf_page_allocate_geometry(\{p},\{cap},\{s})"
  let args = "\{p},\{cap},\{s},\{k},(used0 : \{w}),(prev0 : \{w})"
  let vars = "∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ k : Num, ∀ used0 : \{w}, ∀ prev0 : \{w}"
  let numeric = [
    @arith.mult_suc(),
    @arith.add_clauses(),
    arith("∀ a : Num, ∀ b : Num, ∀ c : Num, a+b+c == a+(b+c)"),
    arith("∀ a : Num, ∀ b : Num, ∀ c : Num, a-b-c == a-(b+c)"),
  ]
  let _ = lemma(
    "tlsf_page_allocate_work_open",
    "\{vars}, \{geom} && k < tlsf_small_total(s) → tlsf_page_allocate_build(\{args}) == ((h : \{heap}) => ∃ w0 : \{w}, ∃ w1 : \{w}, ∃ w2 : \{w}, tlsf_page_allocate_work(\{args},tlsf_page_allocate_head(p,s,k),w0,w1,w2,h))",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_page_allocate_bounds"), [p, cap, s, k])),
      arw([]),
      strip,
      @tactics.undisch_tac(tm(geom)),
      rw([thm("tlsf_page_allocate_geometry")]),
      strip,
      free_have(
        "12 <= \{n} && \{n}-12 == (s-4)+(\{rem})",
        seq([rw([@arith.mult_suc()]), @int.asm_arith_tac]),
      ),
      free_have(
        "\{a}+12+(s-4) == val(p)+32+(8+s)*SUC(k)",
        seq([rw([@arith.mult_suc()]), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(inst(thm("tlsf_page_allocate_words3"), [a, n])),
      arw([]),
      @tactics.disch_tac,
      rw([thm("tlsf_page_allocate_build"), thm("tlsf_page_allocate_work")]),
      arw([]),
      rw(
        [inst(thm("tlsf_bytes_split"), ["\{a}+12", "(s : Num)-4", rem])] +
        lift_rws(),
      ),
      arw(
        [
          thm("star_assoc"),
          thm("star_comm"),
          thm("star_left_comm"),
          thm("star_emp_hr"),
          thm("star_emp_hl"),
        ] +
        numeric +
        lift_rws(),
      ),
    ]),
  )
  let _ = lemma(
    "tlsf_page_allocate_work_close",
    "\{vars}, \{geom} && k < tlsf_small_total(s) → tlsf_page_allocate_work(\{args},\{b},word(4),p,tlsf_page_allocate_head(p,s,k)) == tlsf_page_allocate_build(p,cap,s,SUC(k),used0,prev0)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(inst(thm("tlsf_page_allocate_bounds"), [p, cap, s, k])),
      arw([]),
      strip,
      rw([
        thm("tlsf_page_allocate_work"),
        thm("tlsf_page_allocate_build"),
        thm("tlsf_istar"),
        thm("tlsf_page_allocate_slot"),
        thm("tlsf_page_allocate_head_suc"),
      ]),
      arw(
        [
          thm("star_assoc"),
          thm("star_comm"),
          thm("star_left_comm"),
          thm("star_emp_hr"),
          thm("star_emp_hl"),
        ] +
        numeric,
      ),
    ]),
  )
}
