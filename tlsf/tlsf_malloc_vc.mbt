///|
fn malloc_case_variables() -> Array[(String, String)] {
  malloc_g_variables() +
  malloc_publication_variables() +
  [("pop", "Num"), ("push", "Num")] +
  page_model_variables() +
  [
    ("n", w32),
    ("before", heap),
    ("fp", rty),
    ("l0", "Value"),
    ("l1", "Value"),
    ("l2", "Value"),
    ("l3", "Value"),
    ("l4", "Value"),
    ("p", w32),
    ("b", w32),
    ("bs", "List[" + w32 + "]"),
    ("z", "List[" + w32 + "]"),
    ("i", "Num"),
  ]
}

///|
fn malloc_extra_rewrites() -> Array[@kernel.Thm] {
  [
    thm("tlsf_try_malloc_post"),
    thm("tlsf_malloc_ro"),
    thm("tlsf_small_head"),
    @lists.hd(),
    @lists.cons_11(),
    @lists.not_cons_nil(),
    @lists.append(),
    @words.word_ule_v1(),
    @words.word_ugt_v1(),
    @words.word_uge_v1(),
    @words.val_word(),
    @words.dimindex_32(),
    @arith.add_clauses(),
    @arith.le_refl(),
  ]
}

///|
fn malloc_vc(extra~ : Array[@kernel.Thm] = []) -> @tactics.Tactic raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rws = malloc_extra_rewrites() + extra
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let norm = (g : @tactics.Goal) => {
    let eqs = g.0
      .to_array()
      .map(x => x.1)
      .filter(th => {
        if args_of(@kernel.concl(th), "=", 2) is Some([lhs, _]) {
          ["val", "DIV", "word_jshl"].contains(head_name(lhs)) ||
          lhs is @kernel.Term::Var(_, _)
        } else {
          false
        }
      })
    seq([
      @tactics.rule_assum_tac(th => {
        if eqs.any(e => @kernel.concl(e) == @kernel.concl(th)) {
          th
        } else {
          @simp.rewrite_rule(ths(eqs + rws))(th)
        }
      }),
      @simp.rewrite_tac(ths(eqs)),
    ])(g)
  }
  let simple = seq([
    arw(rws),
    @tactics.conv_tac(@calc_num.num_reduce_conv),
    @tactics.try_tac(
      @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
    ),
    arw(rws),
  ])
  let witness = (g : @tactics.Goal) => {
    if !@basics.is_exists(g.1) {
      return @tactics.no_tac(g)
    }
    @tactics.first(
      @list.List([
        solve(
          seq([
            @tactics.exists_tac(tm("(NIL : List[Value])")),
            simple,
            @tactics.first(
              @list.List([
                solve(@int.asm_arith_tac),
                solve(page_publish_atomic([])),
              ]),
            ),
          ]),
        ),
        @tactics.first_assum(th => {
          if args_of(@kernel.concl(th), "tlsf_malloc_result", 8) is Some(a) {
            seq([
              @tactics.exists_tac(a[4]),
              simple,
              @tactics.try_tac(page_publish_atomic([])),
            ])
          } else {
            @tactics.no_tac
          }
        }),
      ]),
    )(g)
  }
  seq([
    gen,
    @tactics.repeat_tac(@tactics.strip_tac),
    beta_goal(),
    @tactics.try_tac(solve(arw([]))),
    norm,
    simple,
    @tactics.first(
      @list.List([
        solve(@int.asm_arith_tac),
        solve(page_publish_atomic([])),
        solve(witness),
        solve(
          seq([
            @tactics.exists_tac(tm("(NIL : List[Value])")),
            simple,
            @tactics.try_tac(
              @tactics.conv_tac(@equal.top_depth_conv(@ind_types.unwind_conv)),
            ),
            simple,
            @tactics.first(
              @list.List([
                solve(@int.asm_arith_tac),
                solve(page_publish_atomic([])),
                solve(witness),
              ]),
            ),
          ]),
        ),
      ]),
    ),
  ])
}

///|
fn malloc_export_arguments(
  v : String,
  a : Array[String],
  n : String,
  kind : String,
) -> Array[String] {
  let w = w32
  let lw = "List[" + w + "]"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let s = if kind == "fresh" { "(s : Num)" } else { "8*val(" + cls + ")" }
  malloc_publication_variables().map(x => {
    if x.0 == "original" {
      malloc_original(v, n)
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  }) +
  a +
  [
    "(p : " + w + ")",
    "(b : " + w + ")",
    "(bs : " + lw + ")",
    "val(" + cls + ")",
    s,
    "(i : Num)",
    "(used0 : " + w + ")",
    "(prev0 : " + w + ")",
    "(l1 : Value)",
    "(l2 : Value)",
    "(l3 : Value)",
    "(l4 : Value)",
    "(fp : " + rty + ")",
    "(z : " + lw + ")",
    "(before : " + heap + ")",
    n,
  ]
}
