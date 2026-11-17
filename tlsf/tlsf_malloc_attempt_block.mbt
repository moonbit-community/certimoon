// The two inlined full_malloc attempts exit their surrounding result block.

///|
fn prove_tlsf_malloc_attempt_blocks() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let gvars = malloc_g_variables()
  let params = (a + [n, "(before : " + heap + ")", "(fp : " + rty + ")"]).join(
    ",",
  )
  let arity = lemma(
    "tlsf_try_malloc_post_arity",
    page_quantify(
      page_model_variables() +
      [
        ("n", w32),
        ("before", heap),
        ("fp", rty),
        ("res", "List[Value]"),
        ("gs", "List[Value]"),
        ("ms", "Num"),
        ("h", heap),
      ],
    ) +
    "tlsf_try_malloc_post(" +
    params +
    ")((res : List[Value]),(gs : List[Value]),(ms : Num),(h : " +
    heap +
    ")) → LENGTH(res) == 1",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("tlsf_try_malloc_post")])),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      subst_vars(),
      @simp.rewrite_tac(ths([@lists.length()])),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  for v in ["first", "retry"] {
    let q = malloc_attempt_post(v, a, n)
    let lc = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let code = "tlsf_malloc_full_" +
      (if v == "first" { "prefix" } else { "retry" }) +
      "(" +
      page_arguments(malloc_env_variables()) +
      ")"
    let args = malloc_case_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
    let chunk = inst(thm("tlsf_malloc_" + v + "_attempt"), args)
    let label = lemma(
      "tlsf_malloc_" + v + "_attempt_label",
      page_quantify(
        page_model_variables() +
        [
          ("n", w32),
          ("before", heap),
          ("fp", rty),
          ("original", "Value"),
          ("vs", "List[Value]"),
          ("lc", "List[Value]"),
          ("gs", "List[Value]"),
          ("ms", "Num"),
          ("h", heap),
        ],
      ) +
      "(LENGTH((vs : List[Value])) == 1 && (" +
      q +
      ")(vs,lc,gs,ms,h)) == (" +
      q +
      ")(vs,lc,gs,ms,h)",
      small_meson(ths([arity])),
    )
    let all = lemma(
      "tlsf_malloc_" + v + "_block_g",
      page_quantify(malloc_case_variables()) +
      "val(" +
      n +
      ") <= 4160749568 && (" +
      malloc_helper_natives() +
      ") → sl_triple_g(" +
      malloc_g_env() +
      ",st(NIL," +
      lc +
      "," +
      r +
      ")," +
      code +
      "," +
      q +
      ",NIL)",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @simp.pure_rewrite_tac(ths([thm(head_name(tm(code)))])),
        @tactics.match_mp_tac(thm("sl_block_st_g")),
        beta_goal(),
        @tactics.conv_tac(
          norm_conv(extra=[@equal.beta_rule(label), thm("tbv_results")]),
        ),
        free_apply(
          @simp.pure_rewrite_rule(ths([thm("tlsf_malloc_" + v + "_body")]))(
            chunk,
          ),
        ),
      ]),
    )
    let vars = malloc_case_variables().filter(x => {
      x.0 != "G" && x.0 != "rp" && x.0 != "labels"
    })
    let falseg = "(j : Num) => (P : (List[Value],List[Value],Num," +
      heap +
      ") -> Bool) => (Q : (List[Value],List[Value],Num," +
      heap +
      ") -> Bool) => F"
    let instargs = malloc_case_variables().map(x => {
      if x.0 == "G" {
        falseg
      } else if x.0 == "rp" {
        malloc_false()
      } else {
        "(" + x.0 + " : " + x.1 + ")"
      }
    })
    let _ = lemma(
      "tlsf_malloc_" + v + "_block",
      page_quantify(vars) +
      "val(" +
      n +
      ") <= 4160749568 && (" +
      malloc_helper_natives() +
      ") → sl_triple_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst),st(NIL," +
      lc +
      "," +
      r +
      ")," +
      code +
      "," +
      q +
      ",NIL)",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(thm("sl_triple_m_of_g")),
        @tactics.exists_tac(tm(falseg)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @simp.rewrite_tac(ths([thm("specs_ok")])),
              @meson.meson_tac(ths([])),
            ]),
            free_apply(inst(all, instargs)),
          ]),
        ),
      ]),
    )
  }
  let _ = gvars
}
