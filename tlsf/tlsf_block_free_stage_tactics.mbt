///|
fn block_old_facts(args : Array[String], p : String, b : String) -> String {
  block_backing(args) +
  " && " +
  block_lists(args) +
  " && MEM(" +
  p +
  "," +
  args[8] +
  ") && MEM(" +
  b +
  "," +
  args[12] +
  "(" +
  p +
  ")) && val(" +
  args[0] +
  ") <= 4294965088"
}

///|
fn block_native_hyp() -> String raise {
  let a = block_model_args()
  let w = w32
  let th = inst(
    thm("tlsf_free_all"),
    [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      a[0],
      "(pop : Num)",
      "(push : Num)",
      "(free_idx : Num)",
      "(p : " + w + ")",
      a[1],
    ] +
    a[2:8].to_owned() +
    ["(fp : " + rty + ")", "(NIL : List[Value])", "(NIL : List[Value])"],
  )
  show(@basics.dest_imp(@kernel.concl(th)).0)
}

///|
fn block_prepare(
  args : Array[String],
  p : String,
  b : String,
) -> @tactics.Tactic raise {
  let geometry = [3, 4, 8, 9, 10, 11, 12, 1, 13, 14].map(i => args[i])
  let backingargs = [3, 4, 8, 9, 10, 11, 12, 1].map(i => args[i])
  let u = block_usage(args, p)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  seq([
    free_have(
      "tlsf_count(" + p + "," + args[8] + ") == 1",
      seq([
        @tactics.undisch_tac(tm(block_lists(args))),
        rw([thm("tlsf_small_lists_ok")]),
        small_meson(ths([])),
      ]),
    ),
    g => {
      @tactics.strip_assume_tac(
        block_under(
          inst(thm("tlsf_small_page_member_geometry"), geometry + [p]),
          g,
        ),
      )(g)
    },
    g => {
      @tactics.strip_assume_tac(
        block_under(
          inst(thm("tlsf_small_live_release_usage"), geometry + [p, b]),
          g,
        ),
      )(g)
    },
    g => {
      @tactics.strip_assume_tac(
        block_under(
          inst(thm("tlsf_small_capacity"), [args[9] + "(" + p + ")"]),
          g,
        ),
      )(g)
    },
    free_have(u + " <= 66", @int.asm_arith_tac),
    g => {
      @tactics.assume_tac(
        block_under(
          inst(thm("tlsf_small_backing_release"), backingargs + [p, b]),
          g,
        ),
      )(g)
    },
    g => {
      @tactics.assume_tac(
        block_under(inst(thm("tlsf_small_partial_geometry"), geometry), g),
      )(g)
    },
    free_have(
      "∀ q : \{w32}, MEM(q," +
      args[14] +
      "(DIV(" +
      args[9] +
      "(" +
      p +
      "),8))) → !(q == word(0)) && val(q)+32 <= 4294967296",
      small_meson(ths([])),
    ),
  ])
}

///|
fn block_model_case(
  which : String,
  args : Array[String],
  p : String,
  g : @tactics.Goal,
) -> Array[@kernel.Thm] raise {
  let params = [8, 9, 11, 12, 14].map(i => args[i]) + [p]
  @bool.conjuncts_rule(
    block_under(inst(thm("tlsf_block_free_model_" + which), params), g),
  ).to_array()
}

///|
fn block_flag(
  args : Array[String],
  p : String,
  one : Bool,
  taken : Bool,
  g : @tactics.Goal,
) -> @kernel.Thm raise {
  let u = block_usage(args, p)
  let rhs = if one { "1" } else { block_total(args, p) }
  let rule = if one {
    inst(thm("tlsf_small_usage_one_flag"), [u])
  } else {
    inst(thm("tlsf_small_usage_flag"), [u, rhs])
  }
  let condition = u + " == " + rhs
  let fact = @kernel.assume_rule(
    tm(if taken { condition } else { "!(" + condition + ")" }),
  )
  @equal.conv_rule(
    @equal.rand_conv(@simp.rewrite_conv(ths([fact]))),
    block_under(rule, g),
  )
}

///|
fn block_if(
  taken : Bool,
  flag : @kernel.Thm,
  body : @tactics.Tactic,
) -> @tactics.Tactic raise {
  seq([
    @tactics.match_mp_tac(
      thm("tlsf_block_free_if_" + (if taken { "taken" } else { "skipped" })),
    ),
    @tactics.thenl(
      @tactics.conj_tac,
      @list.List([
        seq([
          @simp.rewrite_tac(ths([flag])),
          @tactics.conv_tac(@words.word_reduce_conv),
        ]),
        seq([@tactics.gen_tac, body]),
      ]),
    ),
  ])
}

///|
fn block_same_post(
  eqs : Array[@kernel.Thm],
  params : Array[String],
) -> @tactics.Tactic raise {
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  seq([
    gen,
    rw([thm("st")] + lift_rws()),
    beta_goal(),
    rw(lift_rws()),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    arw([]),
    g => {
      let all = @basics.strip_comb(g.1).1.to_array()
      guard head_name(g.1) == "tlsf_block_free_post" && all.length() == 25 else {
        raise Failure("block_same_post: expected allocator post")
      }
      let states = all[20:].to_owned().map(show)
      let fold = @simp.rewrite_rule(ths(eqs))(
        inst(thm("tlsf_block_free_post_same"), params + states),
      )
      seq([
        free_apply(fold),
        beta_goal(),
        arw([]),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        arw(ac),
      ])(g)
    },
  ])
}
