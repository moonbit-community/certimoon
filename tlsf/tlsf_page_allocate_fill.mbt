// Compose the bounded initialization loop with the initial and final words.

///|
fn page_conseq(
  path : @kernel.Thm,
  pre : @tactics.Tactic,
  post : @tactics.Tactic,
) -> @tactics.Tactic raise {
  let path = @bool.spec_all(path)
  let c = @kernel.concl(path)
  let body = if @basics.is_imp(c) { @basics.dest_imp(c).1 } else { c }
  let a = args_of(body, "sl_triple", 3).unwrap()
  seq([
    @tactics.match_mp_tac(thm("sl_conseq")),
    @tactics.exists_tac(a[0]),
    @tactics.exists_tac(a[2]),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        pre,
        seq([
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([free_apply(path), post]),
          ),
        ]),
      ]),
    ),
  ])
}

///|
fn prove_tlsf_page_allocate_fill() -> Unit raise {
  let w = w32
  let p = "(p : \{w})"
  let s = "(s : \{w})"
  let cap = "(cap : Num)"
  let total = "tlsf_small_total(val(\{s}))"
  let i = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let head = "tlsf_page_allocate_head(\{p},val(\{s}),\{total})"
  let build = (n : String) => {
    "tlsf_page_allocate_build(\{p},\{cap},val(\{s}),\{n},(used0 : \{w}),(prev0 : \{w}))"
  }
  let own = (x : String) => {
    "(gs : List[Value]) => (ms : Num) => \{small_star([x,"(fp : "+rty+")(gs,ms)"])}"
  }
  let done = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ scratch : Value, vs == NIL && lc == [\{i(s)},\{i(p)},\{i(head)},\{i("word("+total+")")},scratch,\{i("word("+total+")")}] && \{small_star([build(total),"(fp : "+rty+")(gs,ms)"])}(h)"
  let q = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs == [\{i(p)}] && star(tlsf_page_allocate_fresh(\{p},\{cap},val(\{s})),(fp : \{rty})(gs,ms),h)"
  let geom = "tlsf_page_allocate_geometry(\{p},\{cap},val(\{s}))"
  let vars = "∀ take_idx : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ used0 : \{w}, ∀ prev0 : \{w}, ∀ fp : \{rty}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let last = sym_prove(
    "tlsf_page_allocate_result",
    "\{vars}, \{geom} → sl_triple(\{done},[Local_get(1)],\{q})",
    [],
    [
      seq([
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        ent_tac(
          [
            thm("tlsf_page_allocate_fresh"),
            thm("star_emp_hr"),
            thm("star_emp_hl"),
          ],
          ["(used0 : " + w + ")", "(prev0 : " + w + ")"],
        ),
      ]),
    ],
    kind="lemma",
  )
  let args = [
    "(take_idx : Num)",
    p,
    cap,
    s,
    "(used0 : " + w + ")",
    "(prev0 : " + w + ")",
    "(fp : " + rty + ")",
  ]
  let loopth = inst(thm("tlsf_page_allocate_loop_build"), args)
  let looptr = args_of(
    @basics.dest_imp(@kernel.concl(loopth)).1,
    "sl_triple",
    3,
  ).unwrap()
  let code = "APPEND(tlsf_page_allocate_loop((take_idx : Num)),[Local_get(1)])"
  let joined = lemma(
    "tlsf_page_allocate_loop_result",
    "\{vars}, \{geom} → sl_triple(\{show(looptr[0])},\{code},\{q})",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.match_mp_tac(thm("sl_seq")),
      @tactics.exists_tac(looptr[2]),
      @tactics.conj_tac,
      @tactics.first(
        @list.List([
          solve(free_apply(loopth)),
          solve(free_apply(inst(last, args))),
        ]),
      ),
    ]),
  )
  let lc = "[\{i(s)},\{i(p)},\{i("word_add("+p+",word(32))")},\{i("word(1)")},(l4 : Value),\{i("word("+total+")")}]"
  let entry = lemma(
    "tlsf_page_allocate_loop_entry",
    "\{vars}, ∀ l4 : Value, \{geom} → sl_triple(st(NIL,\{lc},\{own(build("1"))}),\{code},\{q})",
    seq([
      gen,
      @tactics.disch_tac,
      free_have(
        "1 <= \{total}",
        seq([
          @tactics.undisch_tac(tm(geom)),
          rw([thm("tlsf_page_allocate_geometry")]),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @tactics.mp_tac(inst(thm("tlsf_small_capacity"), ["val(" + s + ")"])),
          arw([]),
          @int.asm_arith_tac,
        ]),
      ),
      page_conseq(
        inst(joined, args),
        ent_tac([thm("tlsf_page_allocate_head_one"), @arith.le_refl()], [
          "1", "(l4 : Value)",
        ]),
        same_tac(),
      ),
    ]),
  )
  let entrypath = inst(entry, args + ["(l4 : Value)"])
  let begin = inst(thm("tlsf_page_allocate_begin_build"), [
    "(take_idx : Num)",
    p,
    cap,
    s,
    "(l2 : Value)",
    "(l3 : Value)",
    "(l4 : Value)",
    "(l5 : Value)",
    "(fp : " + rty + ")",
  ])
  let begintr = args_of(
    @basics.dest_imp(@kernel.concl(begin)).1,
    "sl_triple",
    3,
  ).unwrap()
  let fillvars = "∀ take_idx : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : \{w}, ∀ l2 : Value, ∀ l3 : Value, ∀ l4 : Value, ∀ l5 : Value, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_page_allocate_fill_all",
    "\{fillvars}, \{geom} → sl_triple(\{show(begintr[0])},tlsf_page_allocate_fill(take_idx),\{q})",
    seq([
      gen,
      @tactics.disch_tac,
      rw([thm("tlsf_page_allocate_fill")]),
      @tactics.subst1_tac(
        @equal.gsym(
          @simp.rewrite_conv(
            ths([
              thm("tlsf_page_allocate_begin"),
              thm("tlsf_page_allocate_loop"),
              @lists.append(),
            ]),
          )(
            tm(
              "APPEND(tlsf_page_allocate_begin((take_idx : Num))," + code + ")",
            ),
          ),
        ),
      ),
      @tactics.match_mp_tac(thm("sl_seq")),
      @tactics.exists_tac(begintr[2]),
      @tactics.thenl(
        @tactics.conj_tac,
        @list.List([
          free_apply(begin),
          by_path(entrypath, "T", [], [], [], [
            "(used0 : " + w + ")",
            "(prev0 : " + w + ")",
          ]),
        ]),
      ),
    ]),
  )
}
