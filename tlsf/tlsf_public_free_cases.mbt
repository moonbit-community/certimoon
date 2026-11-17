///|
fn public_free_entry(
  a : Array[String],
  ptr : String,
  l1 : String,
  l2 : String,
  fp : String,
) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => vs == NIL && lc == [" +
  malloc_i(ptr) +
  "," +
  l1 +
  "," +
  l2 +
  "] && tlsf_public_free_pre(" +
  (a + [ptr, fp]).join(",") +
  ")([" +
  malloc_i(ptr) +
  "],gs,ms,h)"
}

///|
fn public_free_cases(
  a : Array[String],
  ptr : String,
  l1 : String,
  l2 : String,
  fp : String,
) -> String {
  let b = "(b : " + w32 + ")"
  let p = "(p : " + w32 + ")"
  let lc = "[" + malloc_i(ptr) + "," + l1 + "," + l2 + "]"
  let st = (r : String) => {
    "st(NIL," +
    lc +
    "," +
    r +
    ")((vs : List[Value]),(lc : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    "))"
  }
  let facts = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && " +
    block_lists(a)
  let large = "∃ b : " +
    w32 +
    ", (" +
    facts +
    " && MEM(" +
    b +
    "," +
    a[3] +
    ") && !MEM(" +
    b +
    "," +
    a[8] +
    ") && tlsf_used(" +
    a[4] +
    "(" +
    b +
    ")) && " +
    ptr +
    " == word_add(" +
    b +
    ",word(8))) && " +
    st(public_free_r(a, b, "val(tlsf_size(" + a[4] + "(" + b + ")))", fp))
  let small = "∃ p : " +
    w32 +
    ", ∃ b : " +
    w32 +
    ", (" +
    facts +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    b +
    "," +
    a[12] +
    "(" +
    p +
    ")) && " +
    ptr +
    " == word_add(" +
    b +
    ",word(8))) && " +
    st(public_free_r(a, b, a[9] + "(" + p + ")", fp))
  let null = "(" +
    facts +
    " && " +
    ptr +
    " == word(0)) && " +
    st(malloc_frame(a, fp, ""))
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => (" +
  null +
  ") || ((" +
  large +
  ") || (" +
  small +
  "))"
}

///|
fn public_free_allocator_facts(a : Array[String]) -> @tactics.Tactic raise {
  let facts = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a) +
    " && " +
    block_lists(a)
  free_have(facts, g => {
    let mut selected : (Array[@kernel.Term], @kernel.Term)? = None
    for (_, th) in g.0 {
      if args_of(@kernel.concl(th), "star", 3) is Some(parts) {
        let factors = malloc_star_factors(parts[0]) +
          malloc_star_factors(parts[1])
        if factors.any(t => head_name(t) == "tlsf_allocator") {
          selected = Some((factors, parts[2]))
          break
        }
      }
    }
    guard selected is Some((factors, h)) else {
      raise Failure("public free entry: no allocator")
    }
    let client = small_star(
      factors.filter(t => head_name(t) != "tlsf_allocator").map(show),
    )
    seq([
      free_apply(
        inst(thm("tlsf_malloc_allocator_facts"), a + [client, show(h)]),
      ),
      @tactics.first_x_assum(th => {
        if head_name(@kernel.concl(th)) == "star" {
          @tactics.mp_tac(th)
        } else {
          @tactics.no_tac
        }
      }),
      @simp.asm_rewrite_tac(ths(malloc_ac())),
    ])(g)
  })
}

///|
fn prove_tlsf_public_free_cases() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let ptr = "(ptr : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let l1 = "(l1 : Value)"
  let l2 = "(l2 : Value)"
  let m = "(m : " + w + ")"
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let frame = seq([
    rw([thm("st")]),
    arw([]),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    arw(malloc_ac()),
  ])
  let _ = lemma(
    "tlsf_public_free_entry_cases",
    page_quantify(
      page_model_variables() +
      [
        ("ptr", w),
        ("l1", "Value"),
        ("l2", "Value"),
        ("fp", rty),
        ("vs", "List[Value]"),
        ("lc", "List[Value]"),
        ("gs", "List[Value]"),
        ("ms", "Num"),
        ("h", heap),
      ],
    ) +
    "(" +
    public_free_entry(a, ptr, l1, l2, fp) +
    ")((vs : List[Value]),(lc : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    ")) → (" +
    public_free_cases(a, ptr, l1, l2, fp) +
    ")(vs,lc,gs,ms,h)",
    () => {
      seq([
        gen,
        beta_goal(),
        rw([thm("tlsf_public_free_pre"), thm("tlsf_malloc_owned")]),
        strip,
        public_free_allocator_facts(a),
        subst_vars(),
        arw([]),
        @tactics.first(
          @list.List([
            solve(seq([@tactics.disj1_tac, frame])),
            solve(
              seq([
                @tactics.disj2_tac,
                @tactics.disj1_tac,
                @tactics.exists_tac(tm(m)),
                arw([]),
                g => {
                  @tactics.strip_assume_tac(
                    block_under(
                      inst(thm("tlsf_public_free_block_geometry"), a + [m]),
                      g,
                    ),
                  )(g)
                },
                free_have(
                  "val(word_add(" + m + ",word(8))) == val(" + m + ")+8",
                  seq([
                    @logic.match_mp_tac(thm("val_add_small")),
                    @tactics.undisch_tac(
                      tm(
                        "tlsf_block_ok(val(" +
                        m +
                        ")," +
                        a[1] +
                        "," +
                        m +
                        "," +
                        a[4] +
                        ")",
                      ),
                    ),
                    rw([thm("tlsf_block_ok")]),
                    strip,
                    @int.asm_arith_tac,
                  ]),
                ),
                frame,
              ]),
            ),
            solve(
              seq([
                @tactics.disj2_tac,
                @tactics.disj2_tac,
                @tactics.exists_tac(tm(p)),
                @tactics.exists_tac(tm(b)),
                arw([]),
                g => {
                  @tactics.strip_assume_tac(
                    block_under(
                      inst(thm("tlsf_public_free_small_geometry"), a + [p, b]),
                      g,
                    ),
                  )(g)
                },
                frame,
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
