///|
fn malloc_fresh_frame(
  a : Array[String],
  p : String,
  s : String,
  used : String,
  prev : String,
  fp : String,
) -> String {
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let build = "tlsf_page_allocate_build(" +
    [p, cap, s, "tlsf_small_total(" + s + ")", used, prev].join(",") +
    ")"
  "(gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => ms == " +
  a[1] +
  " && " +
  small_star([
    build,
    "tlsf_allocator(" + a.join(",") + ")",
    "(" + fp + ")(gs,ms)",
  ]) +
  "(h)"
}

///|
fn malloc_star_factors(t : @kernel.Term) -> Array[@kernel.Term] {
  if args_of(t, "star", 2) is Some([a, b]) {
    malloc_star_factors(a) + malloc_star_factors(b)
  } else if head_name(t) == "emp" {
    []
  } else {
    [t]
  }
}

///|
fn prove_tlsf_malloc_head() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let fp = "(fp : " + rty + ")"
  let used = "(used0 : " + w + ")"
  let prev = "(prev0 : " + w + ")"
  let r = malloc_fresh_frame(a, p, s, used, prev, fp)
  let addr = "word_add(" + p + ",word(20))"
  let ready = publish_ready(a, p, b, bs, s, "(NIL : " + lw + ")")
  let cond = ready +
    " && (i : Num) < tlsf_small_total(" +
    s +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    s +
    ",i) && REVERSE(tlsf_small_slots(" +
    p +
    "," +
    s +
    ",tlsf_small_total(" +
    s +
    "))) == CONS(" +
    b +
    "," +
    bs +
    ")"
  let modelvars = page_model_variables() +
    [
      ("p", w),
      ("b", w),
      ("bs", lw),
      ("s", "Num"),
      ("i", "Num"),
      ("used0", w),
      ("prev0", w),
      ("fp", rty),
    ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let read = lemma(
    "st_malloc_fresh_head",
    page_quantify(modelvars + [("v", "List[Value]"), ("lc", "List[Value]")]) +
    cond +
    " → sl_triple(st(APPEND((v : List[Value]),[" +
    malloc_i(addr) +
    "]),(lc : List[Value])," +
    r +
    "),[Load(T_i32,NONE,2,0)],st(APPEND(v,[" +
    malloc_i(b) +
    "]),lc," +
    r +
    "))",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.match_mp_tac(
        inst(thm("st_load_read"), [
          "(v : List[Value])", "(lc : List[Value])", r, addr, b, "2", "0",
        ]),
      ),
      free_have(
        "val(" + addr + ") == val(" + p + ")+20",
        seq([
          @tactics.match_mp_tac(thm("val_add_small")),
          @tactics.undisch_tac(tm(ready)),
          rw([thm("tlsf_small_page_ok")]),
          @tactics.repeat_tac(@tactics.strip_tac),
          @int.asm_arith_tac,
        ]),
      ),
      g => {
        let view = block_under(
          inst(thm("tlsf_page_publish_fresh_view"), [
            a[1],
            p,
            cap,
            s,
            b,
            bs,
            "(i : Num)",
            used,
            prev,
          ]),
          g,
        )
        let factors = malloc_star_factors(@equal.rhs(@kernel.concl(view)))
        let rest = (factors[:2].to_owned() + factors[3:].to_owned()).map(show)
        let frame = small_star(
          rest +
          [
            "tlsf_allocator(" + a.join(",") + ")",
            "(" + fp + ")((gs : List[Value]),(ms : Num))",
          ],
        )
        ent_tac(
          [thm("has_i32"), view, @arith.add_clauses()] +
          g.0.to_array().map(x => x.1),
          [frame],
        )(g)
      },
    ]),
  )
  let chunk = @simp.rewrite_rule(ths([@lists.append()]))(
    @bool.spec(
      tm("(NIL : List[Value])"),
      inst(read, modelvars.map(x => "(" + x.0 + " : " + x.1 + ")")),
    ),
  )
  let vars = malloc_publication_variables() +
    modelvars +
    [("l1", "Value"), ("l3", "Value"), ("l4", "Value")]
  let same = seq([gen, @tactics.repeat_tac(@tactics.strip_tac), arw([])])
  for v in malloc_variant_names() {
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_fresh_head",
        page_quantify(vars) +
        cond +
        " → sl_triple(st(NIL," +
        malloc_locals(v, [
          malloc_i(p),
          "(l1 : Value)",
          malloc_i("word(" + s + ")"),
          "(l3 : Value)",
          "(l4 : Value)",
        ]) +
        "," +
        r +
        ")," +
        malloc_part(v, "head") +
        ",st([" +
        malloc_i(b) +
        "]," +
        malloc_locals(v, [
          malloc_i(p),
          malloc_i(b),
          malloc_i("word(" + s + ")"),
          malloc_i(addr),
          "(l4 : Value)",
        ]) +
        "," +
        r +
        "))",
        [],
        [same],
        chunks=[chunk],
        kind="lemma",
      ),
    )
  }
}
