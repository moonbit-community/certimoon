///|
fn define_tlsf_malloc_ensure_post() -> Unit raise {
  let a = block_model_args()
  let fp = "(fp : " + rty + ")"
  let n = "(n : " + w32 + ")"
  let failure = "res == [" +
    malloc_i("word(0)") +
    "] && (" +
    malloc_frame(a, fp, "(before : " + heap + ")") +
    ")(gs,ms,h)"
  let newer = malloc_fresh_args(a)
  newer[1] = "(ms : Num)"
  let ex = page_model_variables()[2:8]
    .to_owned()
    .map(x => "∃ " + x.0 + "2 : " + x.1 + ", ")
    .join("")
  let success = "res == [" +
    malloc_i("word(1)") +
    "] && " +
    a[1] +
    " <= ms && (" +
    ex +
    "star(tlsf_allocator(" +
    newer.join(",") +
    "),(" +
    fp +
    ")((gs : List[Value])," +
    a[1] +
    "),(h : " +
    heap +
    ")))"
  def(
    "tlsf_malloc_ensure_post",
    "tlsf_malloc_ensure_post(" +
    (a + [n, "(before : " + heap + ")", fp]).join(",") +
    ") == ((res : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (" +
    failure +
    ") || (" +
    success +
    "))",
  )
}

///|
fn prove_tlsf_malloc_ensure_post() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let ms = "(ms : Num)"
  let gs = "(gs : List[Value])"
  let h = "(h : " + heap + ")"
  let bfr = "(before : " + heap + ")"
  let small = "tlsf_small(" +
    [a[0], a[4], a[8], a[9], a[10], a[11], a[12], a[13], a[14]].join(",") +
    ")"
  let sf = "(gs : List[Value]) => (ms : Num) => star(" +
    small +
    ",(" +
    fp +
    ")(gs,ms))"
  let nh = "tlsf_grow_headers(" +
    a[4] +
    "," +
    a[2] +
    "," +
    a[1] +
    "," +
    ms +
    ")"
  let nx = "tlsf_grow_chain(" +
    a[3] +
    "," +
    a[4] +
    "," +
    a[2] +
    "," +
    a[1] +
    ")"
  let nt = "tlsf_grow_top(" + a[4] + "," + a[2] + "," + a[1] + ")"
  let newer = a.copy()
  newer[1] = ms
  newer[2] = nt
  newer[3] = nx
  newer[4] = nh
  for i in [5, 6, 7] {
    newer[i] = "(" +
      page_model_variables()[i].0 +
      "2 : " +
      page_model_variables()[i].1 +
      ")"
  }
  let retained = "∀ p : " +
    w +
    ", MEM(p," +
    a[8] +
    ") → MEM(p," +
    nx +
    ") && tlsf_used((" +
    nh +
    ")(p)) && tlsf_size((" +
    nh +
    ")(p)) == tlsf_size(" +
    a[4] +
    "(p))"
  let vars = page_model_variables() +
    [
      ("n", w),
      ("before", heap),
      ("fp", rty),
      ("res", "List[Value]"),
      ("gs", "List[Value]"),
      ("ms", "Num"),
      ("h", heap),
    ]
  let source = "tlsf_ensure_post(" +
    ([a[0], n] + a[1:8].to_owned() + [bfr, sf]).join(",") +
    ")((res : List[Value])," +
    gs +
    "," +
    ms +
    "," +
    h +
    ")"
  let target = "tlsf_malloc_ensure_post(" +
    (a + [n, bfr, fp]).join(",") +
    ")((res : List[Value])," +
    gs +
    "," +
    ms +
    "," +
    h +
    ")"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_ensure_post_result",
    page_quantify(vars) +
    physical +
    " && " +
    block_backing(a) +
    " && " +
    source +
    " → " +
    target,
    seq([
      gen,
      rw([thm("tlsf_ensure_post")]),
      strip,
      rw([thm("tlsf_malloc_ensure_post")]),
      beta_goal(),
      arw([]),
      @tactics.first(
        @list.List([
          solve(
            seq([
              @tactics.try_tac(@tactics.disj1_tac),
              @tactics.first_x_assum(th => {
                if head_name(@kernel.concl(th)) == "star" {
                  @tactics.mp_tac(th)
                } else {
                  @tactics.no_tac
                }
              }),
              rw([thm("tlsf_allocator")] + lift_rws()),
              arw(malloc_ac()),
            ]),
          ),
          solve(
            seq([
              @tactics.first_x_assum(th => {
                if args_of(@kernel.concl(th), "=", 2) is Some([lhs, rhs]) &&
                  lhs == tm(ms) &&
                  rhs != tm(a[1]) {
                  @tactics.subst1_tac(@equal.gsym(th))
                } else {
                  @tactics.no_tac
                }
              }),
              free_have(
                retained,
                seq([
                  @tactics.x_gen_tac(tm("(p : " + w + ")")),
                  @tactics.disch_tac,
                  g => {
                    @tactics.strip_assume_tac(
                      block_under(
                        inst(
                          thm("tlsf_malloc_backing_used"),
                          a + ["(p : " + w + ")"],
                        ),
                        g,
                      ),
                    )(g)
                  },
                  free_apply(
                    inst(
                      thm("tlsf_malloc_growth_retains"),
                      a + ["(p : " + w + ")", ms],
                    ),
                  ),
                  arw([]),
                ]),
              ),
              free_have(
                block_backing(newer),
                seq([
                  free_apply(
                    inst(
                      thm("tlsf_small_backing_transport"),
                      [a[3], a[4]] + a[8:13].to_owned() + [a[1], nx, nh, ms],
                    ),
                  ),
                  arw([]),
                ]),
              ),
              free_have(
                small +
                " == tlsf_small(" +
                [a[0], nh, a[8], a[9], a[10], a[11], a[12], a[13], a[14]].join(
                  ",",
                ) +
                ")",
                seq([
                  free_apply(
                    inst(
                      thm("tlsf_small_transport"),
                      [a[0]] + a[8:13].to_owned() + [a[4], nh, a[13], a[14]],
                    ),
                  ),
                  gen,
                  @tactics.disch_tac,
                  @tactics.first_assum(th => {
                    @tactics.mp_tac(@bool.spec(tm("(p : " + w + ")"), th))
                  }),
                  arw([]),
                  page_publish_atomic([]),
                ]),
              ),
              @tactics.try_tac(@tactics.disj2_tac),
              arw([]),
              seq(newer[2:8].to_owned().map(x => @tactics.exists_tac(tm(x)))),
              @tactics.first_x_assum(th => {
                if head_name(@kernel.concl(th)) == "star" {
                  @tactics.mp_tac(th)
                } else {
                  @tactics.no_tac
                }
              }),
              rw([thm("tlsf_allocator")] + lift_rws()),
              arw(malloc_ac()),
            ]),
          ),
        ]),
      ),
    ]),
  )
  let _ = lw
}
