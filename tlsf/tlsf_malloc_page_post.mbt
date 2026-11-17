// Expand a newly initialized page into the ghost witnesses used by publication.

///|
fn malloc_fresh_args(a : Array[String]) -> Array[String] {
  let r = a.copy()
  let model = page_model_variables()
  for i in [2, 3, 4, 5, 6, 7] {
    r[i] = "(" + model[i].0 + "2 : " + model[i].1 + ")"
  }
  r
}

///|
fn define_tlsf_malloc_page_ready_post() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let newer = malloc_fresh_args(a)
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "val((s : " + w + "))"
  let cap = "val(tlsf_size(" + newer[4] + "(" + p + ")))"
  let fp = "(fp : " + rty + ")((gs : List[Value]),(ms : Num))"
  let build = "tlsf_page_allocate_build(" +
    [
      p,
      cap,
      s,
      "tlsf_small_total(" + s + ")",
      "(used0 : " + w + ")",
      "(prev0 : " + w + ")",
    ].join(",") +
    ")"
  let query = "tlsf_search((word(1080) : " +
    w +
    ")," +
    a[5] +
    "," +
    a[6] +
    "," +
    a[7] +
    ")"
  let ready = publish_ready(newer, p, b, bs, s, "(NIL : " + lw + ")")
  let choices = [("p", w)] +
    page_model_variables()[2:8].to_owned().map(v => (v.0 + "2", v.1)) +
    [("used0", w), ("prev0", w), ("b", w), ("bs", lw), ("i", "Num")]
  let success = choices.map(x => "∃ " + x.0 + " : " + x.1 + ", ").join("") +
    "res == [" +
    malloc_i(p) +
    "] && !(" +
    query +
    " == word(0)) && !(" +
    p +
    " == word(0)) && !MEM(" +
    p +
    "," +
    a[8] +
    ") && MEM(" +
    p +
    "," +
    newer[3] +
    ") && tlsf_used(" +
    newer[4] +
    "(" +
    p +
    ")) && tlsf_physical_ok(" +
    newer[:5].to_owned().join(",") +
    ") && " +
    block_backing(newer) +
    " && " +
    block_lists(newer) +
    " && tlsf_page_allocate_geometry(" +
    [p, cap, s].join(",") +
    ") && REVERSE(tlsf_small_slots(" +
    p +
    "," +
    s +
    ",tlsf_small_total(" +
    s +
    "))) == CONS(" +
    b +
    "," +
    bs +
    ") && " +
    ready +
    " && (i : Num) < tlsf_small_total(" +
    s +
    ") && " +
    b +
    " == tlsf_small_slot(" +
    p +
    "," +
    s +
    ",i) && !(" +
    b +
    " == word(0)) && " +
    small_star([build, "tlsf_allocator(" + newer.join(",") + ")", fp]) +
    "(h)"
  let failure = "res == [" +
    malloc_i("word(0)") +
    "] && " +
    query +
    " == word(0) && (h : " +
    heap +
    ") == (before : " +
    heap +
    ") && star(tlsf_allocator(" +
    a.join(",") +
    ")," +
    fp +
    ",h)"
  def(
    "tlsf_malloc_page_ready_post",
    "tlsf_malloc_page_ready_post(" +
    (a + ["(s : " + w + ")", "(before : " + heap + ")", "(fp : " + rty + ")"]).join(
      ",",
    ) +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => ms == " +
    a[1] +
    " && ((" +
    failure +
    ") || (" +
    success +
    ")))",
  )
}

///|
fn prove_tlsf_malloc_page_ready_post() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let newer = malloc_fresh_args(a)
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let h = "(h : " + heap + ")"
  let cap = "val(tlsf_size(" + newer[4] + "(" + p + ")))"
  let build = "tlsf_page_allocate_build(" +
    [
      p,
      cap,
      "val(" + s + ")",
      "tlsf_small_total(val(" + s + "))",
      "(used0 : " + w + ")",
      "(prev0 : " + w + ")",
    ].join(",") +
    ")"
  let postargs = (a + [s, "(before : " + heap + ")", fp]).join(",")
  let vars = page_model_variables() +
    [
      ("s", w),
      ("before", heap),
      ("fp", rty),
      ("res", "List[Value]"),
      ("gs", "List[Value]"),
      ("ms", "Num"),
      ("h", heap),
    ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ws = [p] +
    newer[2:8].to_owned() +
    ["(used0 : " + w + ")", "(prev0 : " + w + ")", b, bs, "(i : Num)"]
  // The source is the selected Page::allocate contract, not the expanded target.
  let _ = lemma(
    "tlsf_malloc_page_expand",
    page_quantify(vars) +
    "tlsf_malloc_page_post(" +
    postargs +
    ")(res,gs,ms,h) → tlsf_malloc_page_ready_post(" +
    postargs +
    ")(res,gs,ms,h)",
    () => {
      seq([
        gen,
        rw(
          [thm("tlsf_malloc_page_post"), thm("tlsf_page_allocate_fresh")] +
          lift_rws(),
        ),
        strip,
        rw([thm("tlsf_malloc_page_ready_post")]),
        beta_goal(),
        arw([]),
        @tactics.first(
          @list.List([
            solve(seq([@tactics.try_tac(@tactics.disj1_tac), arw([])])),
            solve(
              seq([
                free_have(
                  "tlsf_physical_ok(" +
                  newer[:5].to_owned().join(",") +
                  ") && " +
                  block_backing(newer) +
                  " && " +
                  block_lists(newer),
                  seq([
                    @logic.match_mp_tac(
                      inst(
                        thm("tlsf_malloc_allocator_facts"),
                        newer +
                        [
                          "star(" +
                          build +
                          ",(" +
                          fp +
                          ")((gs : List[Value]),(ms : Num)))",
                          h,
                        ],
                      ),
                    ),
                    @tactics.first_x_assum(th => {
                      if head_name(@kernel.concl(th)) == "star" {
                        @tactics.mp_tac(th)
                      } else {
                        @tactics.no_tac
                      }
                    }),
                    arw(malloc_ac()),
                  ]),
                ),
                split_conjs(),
                g => {
                  @tactics.strip_assume_tac(
                    block_under(
                      inst(
                        thm("tlsf_malloc_fresh_dispatch"),
                        newer + [p, "val(" + s + ")"],
                      ),
                      g,
                    ),
                  )(g)
                },
                @tactics.try_tac(@tactics.disj2_tac),
                seq(ws.map(x => @tactics.exists_tac(tm(x)))),
                arw([]),
                @tactics.first_x_assum(th => {
                  if head_name(@kernel.concl(th)) == "star" {
                    @tactics.mp_tac(th)
                  } else {
                    @tactics.no_tac
                  }
                }),
                arw(malloc_ac()),
              ]),
            ),
          ]),
        ),
      ])
    },
  )
}
