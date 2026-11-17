// Derive publication's bounds and local-slot witness from existing results.

///|
fn prove_tlsf_page_publish_entry() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let vs = page_model_variables() + [("p", w), ("client", hprop), ("h", heap)]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_publish_large_bounds",
    page_quantify(vs) +
    "star(" +
    block_large(a) +
    ",(client : " +
    hprop +
    "),(h : " +
    heap +
    ")) && MEM(" +
    p +
    "," +
    a[3] +
    ") → val(" +
    a[0] +
    ") <= 4294965088 && " +
    a[1] +
    " <= 4294967296 && val(" +
    p +
    ")+8+val(tlsf_size(" +
    a[4] +
    "(" +
    p +
    "))) <= " +
    a[1],
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(
              thm("tlsf_large_facts_frame"),
              a[:8].to_owned() +
              ["(client : " + hprop + ")", "(h : " + heap + ")"],
            ),
            g,
          ),
        )(g)
      },
      @tactics.undisch_tac(
        tm("tlsf_physical_ok(" + [a[0], a[1], a[2], a[3], a[4]].join(",") + ")"),
      ),
      rw([thm("tlsf_physical_ok")]),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.mp_tac(
          block_under(
            inst(thm("tlsf_layout_members"), [
              a[3],
              "(word(0) : " + w + ")",
              "tlsf_origin(" + a[0] + ")",
              a[1],
              a[2],
              a[4],
              p,
            ]),
            g,
          ),
        )(g)
      },
      rw([thm("tlsf_block_ok")]),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      arw([]),
    ]),
  )
  let _ = lemma(
    "tlsf_page_publish_local_index",
    "∀ lim : Num, ∀ p : " +
    w +
    ", ∀ cap : Num, ∀ s : Num, ∀ b : " +
    w +
    ", ∀ bs : " +
    lw +
    ", ∀ live : " +
    lw +
    ", tlsf_small_page_ok(lim,p,cap,s,CONS(b,bs),NIL,live) → (∃ i : Num, i < tlsf_small_total(s) && b == tlsf_small_slot(p,s,i))",
    seq([
      gen,
      @tactics.disch_tac,
      free_have(
        "tlsf_small_partition((p : " +
        w +
        "),(s : Num),CONS((b : " +
        w +
        "),(bs : " +
        lw +
        ")),NIL,(live : " +
        lw +
        "))",
        seq([
          @tactics.first_x_assum(th => @tactics.mp_tac(th)),
          rw([thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_page_publish_local_unique"), [
          "(p : " + w + ")",
          "(s : Num)",
          "CONS((b : " + w + "),(bs : " + lw + "))",
          "(NIL : " + lw + ")",
          "(live : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([@lists.mem(), thm("tlsf_small_slots_member")]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_page_publish_empty_cached",
    page_quantify(page_model_variables() + [("p", w)]) +
    block_lists(a) +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") && " +
    a[13] +
    "(DIV(" +
    a[9] +
    "(" +
    p +
    "),8)) == NIL → " +
    a[11] +
    "(" +
    p +
    ") == NIL",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @tactics.undisch_tac(tm(block_lists(a))),
      rw([thm("tlsf_small_lists_ok")]),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      page_publish_old_page_facts(p),
      @tactics.mp_tac(
        @bool.ispec(tm(a[11] + "(" + p + ")"), @lists.list_cases()),
      ),
      @tactics.thenl(
        @tactics.disch_then(th => @tactics.disj_cases_tac(th)),
        @list.List([
          seq([arw([])]),
          seq([
            @tactics.first_x_assum(th => {
              if @basics.is_exists(@kernel.concl(th)) {
                @tactics.x_choose_then(tm("(cb : " + w + ")"))(
                  @tactics.x_choose_then(tm("(ct : " + lw + ")"))(th => {
                    @tactics.assume_tac(th)
                  }),
                )(th)
              } else {
                @tactics.no_tac
              }
            }),
            free_have(
              "tlsf_count((cb : " +
              w +
              ")," +
              a[13] +
              "(DIV(" +
              a[9] +
              "(" +
              p +
              "),8))) == 1",
              seq([
                @tactics.first_assum(th => @tactics.match_mp_tac(th)),
                arw([@lists.mem()]),
              ]),
            ),
            @tactics.undisch_tac(
              tm(
                "tlsf_count((cb : " +
                w +
                ")," +
                a[13] +
                "(DIV(" +
                a[9] +
                "(" +
                p +
                "),8))) == 1",
              ),
            ),
            arw([thm("tlsf_small_count_nil")]),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
          ]),
        ]),
      ),
    ]),
  )
}

///|
fn prove_tlsf_page_publish_allocated_ready() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let s = "(s : Num)"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let fresh = "tlsf_page_allocate_fresh(" + p + "," + cap + "," + s + ")"
  let alloc = "tlsf_allocator(" + a.join(",") + ")"
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
  let ready = "tlsf_small_page_ok(" +
    [
      a[1],
      p,
      cap,
      s,
      "REVERSE(tlsf_small_slots(" + p + "," + s + ",tlsf_small_total(s)))",
      "(NIL : " + lw + ")",
      "(NIL : " + lw + ")",
    ].join(",") +
    ")"
  let client = small_star([
    block_pages(a),
    block_table(a),
    build,
    "(client : " + hprop + ")",
  ])
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let _ = lemma(
    "tlsf_page_publish_allocated_ready",
    page_quantify(
      page_model_variables() +
      [("p", w), ("s", "Num"), ("client", hprop), ("h", heap)],
    ) +
    "star(" +
    alloc +
    ",star(" +
    fresh +
    ",(client : " +
    hprop +
    ")),(h : " +
    heap +
    ")) && MEM(" +
    p +
    "," +
    a[3] +
    ") → " +
    ready,
    seq([
      gen,
      @simp.rewrite_tac(
        ths(
          [
            thm("tlsf_allocator_frame"),
            thm("tlsf_small"),
            thm("tlsf_page_allocate_fresh"),
          ] +
          lift_rws(),
        ),
      ),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_have(
        "val(" +
        a[0] +
        ") <= 4294965088 && " +
        a[1] +
        " <= 4294967296 && val(" +
        p +
        ")+8+" +
        cap +
        " <= " +
        a[1],
        seq([
          @tactics.match_mp_tac(
            inst(
              thm("tlsf_page_publish_large_bounds"),
              a + [p, client, "(h : " + heap + ")"],
            ),
          ),
          @tactics.conj_tac,
          @tactics.first(
            @list.List([
              solve(
                seq([
                  @tactics.first_x_assum(th => {
                    if head_name(@kernel.concl(th)) == "star" {
                      @tactics.mp_tac(th)
                    } else {
                      @tactics.no_tac
                    }
                  }),
                  arw(ac),
                ]),
              ),
              solve(arw([])),
            ]),
          ),
        ]),
      ),
      free_apply(inst(thm("tlsf_page_publish_fresh_ready"), [p, cap, s, a[1]])),
    ]),
  )
}
