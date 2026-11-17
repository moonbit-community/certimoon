// Hide the updated allocator model while preserving the complete client frame.

///|
fn public_free_result(a : Array[String], fp : String) -> String {
  "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => (∃ l : List[Value], st([" +
  malloc_i("word(0)") +
  "],l," +
  public_free_state(a, fp) +
  ")(vs,lc,gs,ms,h))"
}

///|
fn public_free_fold() -> @tactics.Tactic {
  g => {
    guard args_of(g.1, "tlsf_public_free_state", 6) is Some(state) else {
      return @tactics.no_tac(g)
    }
    let mut selected : Array[@kernel.Term]? = None
    for (_, th) in g.0 {
      if args_of(@kernel.concl(th), "star", 3) is Some(parts) {
        for
          part in malloc_star_factors(parts[0]) + malloc_star_factors(parts[1]) {
          if args_of(part, "tlsf_allocator", 15) is Some(a) {
            selected = Some(a)
            break
          }
        }
      }
    }
    guard selected is Some(a) else {
      raise Failure("public free: no allocator to fold")
    }
    seq([
      free_apply(
        inst(
          thm("tlsf_public_free_state_current"),
          (a + [state[2], state[3], state[4], state[5]]).map(show),
        ),
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
  }
}

///|
fn prove_tlsf_public_free_post() -> Unit raise {
  let a = block_model_args()
  let fp = "(fp : " + rty + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_public_free_state_current",
    page_quantify(
      page_model_variables() +
      [("fp", rty), ("gs", "List[Value]"), ("ms", "Num"), ("h", heap)],
    ) +
    "(ms : Num) == " +
    a[1] +
    " && star(tlsf_allocator(" +
    a.join(",") +
    ")," +
    fp +
    "((gs : List[Value]),ms),(h : " +
    heap +
    ")) → " +
    public_free_state(a, fp) +
    "(gs,ms,h)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_public_free_state")]),
        strip,
        subst_only("ms"),
        arw([]),
        seq(a[2:].to_owned().map(x => @tactics.exists_tac(tm(x)))),
        arw([]),
      ])
    },
  )
  let vars = malloc_g_variables() + page_model_variables() + [("fp", rty)]
  let source = inst(
    thm("tlsf_public_free_drop"),
    malloc_g_variables().map(v => "(" + v.0 + " : " + v.1 + ")") +
    [public_free_state(a, fp)],
  )
  let _ = lemma(
    "tlsf_public_free_drop_result",
    page_quantify(vars) +
    "sl_triple_g(" +
    malloc_g_env() +
    "," +
    public_free_result(a, fp) +
    ",[Drop]," +
    public_free_post(a, fp) +
    ",(labels : List[" +
    sassn +
    "]))",
    () => {
      seq([
        gen,
        free_g_conseq(
          source,
          seq([
            gen,
            beta_goal(),
            strip,
            @tactics.exists_tac(tm("(lc : List[Value])")),
            rw([thm("st")]),
            arw([]),
          ]),
          same_tac(),
        ),
      ])
    },
  )
}

///|
fn public_free_final_vc(
  extra~ : Array[@kernel.Thm] = [],
) -> @tactics.Tactic raise {
  @tactics.first(
    @list.List([
      solve(public_free_vc(extra~)),
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        beta_goal(),
        @tactics.repeat_tac(@tactics.strip_tac),
        @simp.asm_rewrite_tac(ths([thm("st")] + extra)),
        @tactics.try_tac(subst_vars()),
        @simp.asm_rewrite_tac(ths(extra)),
        public_free_fold(),
      ]),
    ]),
  )
}
