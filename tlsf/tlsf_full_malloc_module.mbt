///|
fn malloc_full_native() -> String {
  "EL(sfunc_ind((inst : Inst),(full_idx : Num)),(fs : List[Cl])) == Func_native((inst : Inst),Tf([T_num(T_i32)],[T_num(T_i32)]),[" +
  Array::make(5, "T_num(T_i32)").join(",") +
  "],tlsf_full_malloc_code(" +
  page_arguments(malloc_env_variables()) +
  "))"
}

///|
fn malloc_full_call_post(
  a : Array[String],
  n : String,
  caller : String,
) -> String {
  let post = "tlsf_full_malloc_post(" +
    (a + [n, "(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => lc == " +
  caller +
  " && " +
  post +
  "(res,gs,ms,h)"
}

///|
fn prove_tlsf_full_malloc_slow_call() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let caller = "(caller : List[Value])"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", fp]).join(",") +
    ")"
  let p = "st([" + malloc_i(n) + "]," + caller + "," + r + ")"
  let q = malloc_full_call_post(a, n, caller)
  let ap = malloc_abort_post(a)
  let facts = "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") && " +
    block_backing(a)
  let strong = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => (" +
    facts +
    ") && (" +
    p +
    ")(vs,lc,gs,ms,h)"
  let vars = malloc_entry_variables() +
    [("full_idx", "Num")] +
    page_model_variables() +
    [("n", w), ("before", heap), ("fp", rty), ("caller", "List[Value]")]
  let bodyvars = malloc_case_variables().filter(x => {
    x.0 != "G" && x.0 != "rp" && x.0 != "labels"
  })
  let zero = malloc_i("word(0)")
  let bodyargs = bodyvars.map(x => {
    if ["l0", "l1", "l2", "l3", "l4"].contains(x.0) {
      zero
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let ts = "[" + Array::make(5, "T_num(T_i32)").join(",") + "]"
  let zs = "[" + Array::make(5, zero).join(",") + "]"
  let post = "tlsf_full_malloc_post(" +
    (a + [n, "(before : " + heap + ")", fp]).join(",") +
    ")"
  let code = "tlsf_full_malloc_code(" +
    page_arguments(malloc_env_variables()) +
    ")"
  let rule = inst(thm("sl_abort_call_value_m"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    malloc_i(n),
    "(full_idx : Num)",
    ts,
    code,
    zs,
    caller,
    r,
    post,
    "tlsf_malloc_state(" + a[0] + "," + a[1] + "," + fp + ")",
  ])
  let cond = "val(" +
    n +
    ") <= 4160749568 && !" +
    malloc_available(a, n) +
    " && (" +
    malloc_full_natives() +
    ") && " +
    malloc_full_native()
  let _ = lemma(
    "tlsf_full_malloc_slow_call",
    page_quantify(vars) +
    cond +
    " → sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    p +
    ",[Call(full_idx)]," +
    q +
    "," +
    ap +
    ")",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @logic.match_mp_tac(thm("sl_abort_pre_m")),
        @tactics.exists_tac(tm(strong)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            seq([
              @tactics.repeat_tac(@tactics.gen_tac),
              @simp.rewrite_tac(ths([thm("st"), thm("tlsf_malloc_ro")])),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              @simp.asm_rewrite_tac(ths([])),
              g => {
                @tactics.strip_assume_tac(
                  block_under(
                    inst(
                      thm("tlsf_malloc_allocator_facts"),
                      a +
                      [
                        "(" + fp + ")((gs : List[Value])," + a[1] + ")",
                        "(h : " + heap + ")",
                      ],
                    ),
                    g,
                  ),
                )(g)
              },
              @simp.asm_rewrite_tac(ths([])),
            ]),
            seq([
              @logic.match_mp_tac(thm("sl_abort_pure_m")),
              @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
              free_have(
                "!(" + n + " == word(0))",
                seq([
                  @tactics.disch_tac,
                  @tactics.undisch_tac(tm("!" + malloc_available(a, n))),
                  @simp.asm_rewrite_tac(ths([])),
                ]),
              ),
              free_have(
                "!(val(" + n + ") == 0)",
                @simp.asm_rewrite_tac(ths([@words.val_eq_0()])),
              ),
              free_have("0 < val(" + n + ")", @int.asm_arith_tac),
              free_apply(rule),
              @tactics.repeat_tac(@tactics.conj_tac),
              @tactics.first(
                @list.List([
                  solve(
                    @simp.rewrite_tac(
                      ths([
                        @wasm.thm("n_zeros"),
                        @wasm.thm("bitzero"),
                        @wasm.thm("bitzero_num"),
                        @wasm.thm("map_option"),
                        @lists.map(),
                        @wasm.thm("those"),
                      ]),
                    ),
                  ),
                  solve(
                    free_apply(
                      inst(thm("tlsf_full_malloc_slow_body"), bodyargs),
                    ),
                  ),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}

///|
fn prove_tlsf_full_malloc_module() -> Unit raise {
  let a = block_model_args()
  let n = "(n : " + w32 + ")"
  let fp = "(fp : " + rty + ")"
  let caller = "(caller : List[Value])"
  let model = page_model_variables() +
    [("n", w32), ("before", heap), ("fp", rty)]
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", fp]).join(",") +
    ")"
  let p = "st([" + malloc_i(n) + "]," + caller + "," + r + ")"
  let strong = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
    heap +
    ") => val(" +
    n +
    ") <= 4160749568 && (" +
    p +
    ")(vs,lc,gs,ms,h)"
  let pre = call_pre(
    "tlsf_try_malloc_pre(" + page_arguments(model) + ")",
    "(NIL : List[Value])",
    caller,
  )
  let post = malloc_full_call_post(a, n, caller)
  let ap = malloc_abort_post(a)
  let vars = malloc_entry_variables() +
    [("full_idx", "Num")] +
    model +
    [("caller", "List[Value]")]
  let env = malloc_entry_variables() + [("d", w32), ("full_idx", "Num")]
  let extras = model.filter(x => x.0 != "d")
  let fast = inst(
    thm("tlsf_full_malloc_fast_all"),
    env.map(x => "(" + x.0 + " : " + x.1 + ")") +
    extras.map(x => "(" + x.0 + " : " + x.1 + ")") +
    ["(NIL : List[Value])", caller],
  )
  let slow = inst(
    thm("tlsf_full_malloc_slow_call"),
    vars.map(x => "(" + x.0 + " : " + x.1 + ")"),
  )
  let cond = "(" + malloc_full_natives() + ") && " + malloc_full_native()
  let _ = lemma(
    "tlsf_full_malloc_all",
    page_quantify(vars) +
    cond +
    " → sl_abort_m((fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)," +
    pre +
    ",[Call(full_idx)]," +
    post +
    "," +
    ap +
    ")",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @logic.match_mp_tac(thm("sl_abort_pre_m")),
        @tactics.exists_tac(tm(strong)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            ent_tac(
              [
                thm("tlsf_try_malloc_pre"),
                thm("tlsf_malloc_ro"),
                @lists.append(),
              ],
              [],
            ),
            seq([
              @logic.match_mp_tac(thm("sl_abort_pure_m")),
              @tactics.disch_tac,
              @class.asm_cases_tac(tm(malloc_available(a, n))),
              @tactics.first(
                @list.List([
                  solve(
                    seq([
                      initialize_abort_conseq(
                        fast,
                        ent_tac(
                          [
                            thm("tlsf_full_malloc_fast_pre"),
                            thm("tlsf_try_malloc_pre"),
                            thm("tlsf_malloc_ro"),
                            @lists.append(),
                          ],
                          [],
                        ),
                        seq([
                          @tactics.repeat_tac(@tactics.gen_tac),
                          beta_goal(),
                          @simp.rewrite_tac(ths([@lists.append()])),
                          @tactics.repeat_tac(@tactics.strip_tac),
                          subst_vars(),
                          @simp.asm_rewrite_tac(ths([])),
                        ]),
                      ),
                    ]),
                  ),
                  solve(free_apply(slow)),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
