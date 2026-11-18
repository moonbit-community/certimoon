// Startup attempts reuse the checked post-initialization dispatch proofs.

///|
fn malloc_start_vars() -> Array[(String, String)] {
  malloc_entry_variables() +
  [("d", w32), ("lim", "Num"), ("n", w32), ("before", heap), ("fp", rty)]
}

///|
fn malloc_start_ready_model() -> Array[String] {
  malloc_start_model(
    "(d : \{w32})",
    "tlsf_initialize_limit((d : \{w32}),(lim : Num))",
  )
}

///|
fn malloc_start_ready_ro() -> String {
  "tlsf_malloc_ro(" +
  (malloc_start_ready_model() + ["(prepared : \{heap})", malloc_start_frozen()]).join(
    ",",
  ) +
  ")"
}

///|
fn malloc_start_ready_attempt(v : String) -> String {
  malloc_attempt_post(v, malloc_start_ready_model(), "(n : \{w32})")
  .replace(old="(before : \{heap})", new="(prepared : \{heap})")
  .replace(old="(fp : \{rty})", new="(" + malloc_start_frozen() + ")")
}

///|
fn malloc_start_attempt_post(v : String) -> String {
  if v == "try" {
    body_post(
      "tlsf_try_malloc_start_post((d : \{w32}),(n : \{w32}),(lim : Num),(before : \{heap}),(fp : \{rty}))",
    )
  } else {
    "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ prepared : \{heap}, (" +
    malloc_start_ready_attempt(v) +
    ")(vs,lc,gs,ms,h)"
  }
}

///|
fn malloc_start_init_abort() -> String {
  "tlsf_initialize_abort((d : \{w32}),(lim : Num),(before : \{heap}),(fp : \{rty}))"
}

///|
fn malloc_start_attempt_cond() -> String raise {
  "tlsf_initialize_valid((d : \{w32}),(lim : Num)) && 0 < val((n : \{w32})) && val(n) <= 4160749568 && " +
  malloc_start_initialize_native() +
  " && " +
  malloc_start_push_native() +
  " && (" +
  malloc_helper_natives() +
  ")"
}

///|
fn startup_attempt_post_vc(v : String) -> @tactics.Tactic raise {
  if v == "try" {
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      beta_goal(),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_apply(
        inst(thm("tlsf_malloc_start_try_outcome"), [
          "(d : \{w32})",
          "(lim : Num)",
          "(n : \{w32})",
          "(before : \{heap})",
          "(fp : \{rty})",
          "(prepared : \{heap})",
          "(vs : List[Value])",
          "(gs : List[Value])",
          "(ms : Num)",
          "(h : \{heap})",
        ]),
      ),
      startup_vc(),
    ])
  } else {
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      beta_goal(),
      @tactics.disch_then(th => @tactics.assume_tac(th)),
      @tactics.exists_tac(tm("(prepared : \{heap})")),
      @simp.asm_rewrite_tac(ths([])),
    ])
  }
}

///|
fn prove_tlsf_malloc_start_attempts() -> Unit raise {
  let vars = malloc_start_vars() +
    [
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]
  let n = "(n : \{w32})"
  for v in ["try", "first"] {
    let q = malloc_start_attempt_post(v)
    let rp = if v == "try" { q } else { malloc_false() }
    let ab = malloc_start_init_abort()
    let locals = malloc_request_locals(
      v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
    )
    let ready = if v == "try" {
      malloc_request_locals(
        v,
        n,
        "(l0 : Value)",
        malloc_i(malloc_start_slot()),
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      )
    } else {
      malloc_request_locals(
        v,
        n,
        malloc_i(malloc_start_slot()),
        "(l1 : Value)",
        "(l2 : Value)",
        "(l3 : Value)",
        "(l4 : Value)",
      )
    }
    let p = "st(NIL," + ready + "," + malloc_start_ready_ro() + ")"
    let args = (malloc_g_variables() +
    malloc_env_variables() +
    [
      ("pop", "Num"),
      ("push", "Num"),
      ("lim", "Num"),
      ("n", w32),
      ("before", heap),
      ("fp", rty),
      ("prepared", heap),
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
    ]).map(x => {
      if x.0 == "G" {
        startup_false_specs()
      } else if x.0 == "rp" {
        rp
      } else if (v == "try" && x.0 == "l1") || (v == "first" && x.0 == "l0") {
        malloc_i(malloc_start_slot())
      } else {
        "(" + x.0 + " : " + x.1 + ")"
      }
    })
    let resume_proof = startup_lemma(
      "tlsf_malloc_" + v + "_start_resume",
      page_quantify(vars + [("prepared", heap)]) +
      malloc_start_attempt_cond() +
      " → tlsf_sl_abort_r(" +
      startup_env() +
      "," +
      rp +
      "," +
      p +
      "," +
      malloc_part(v, "resume") +
      "," +
      q +
      ",[" +
      q +
      "]," +
      ab +
      ")",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @class.asm_cases_tac(tm("val(" + n + ") <= 256")),
        g => {
          let use_case = (part : String) => {
            let source = startup_r_of_g(
              inst(thm("tlsf_malloc_start_" + v + "_" + part), args),
              ab,
            )
            startup_weaken(
              source,
              seq([free_apply(source), startup_vc()]),
              startup_attempt_post_vc(v),
            )
          }
          @tactics.first(
            @list.List([solve(use_case("fresh")), solve(use_case("large"))]),
          )(g)
        },
      ]),
    )
    let initialized = "st(NIL," + ready + "," + malloc_start_initialized() + ")"
    let preparedpre = "(vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => ∃ prepared : \{heap}, " +
      p +
      "(vs,lc,gs,ms,h)"
    let after = startup_lemma(
      "tlsf_malloc_" + v + "_start_dispatch",
      page_quantify(vars) +
      malloc_start_attempt_cond() +
      " → tlsf_sl_abort_r(" +
      startup_env() +
      "," +
      rp +
      "," +
      initialized +
      "," +
      malloc_part(v, "resume") +
      "," +
      q +
      ",[" +
      q +
      "]," +
      ab +
      ")",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        @tactics.match_mp_tac(thm("tlsf_sl_abort_r_conseq")),
        @tactics.exists_tac(tm(preparedpre)),
        @tactics.exists_tac(tm(q)),
        @tactics.exists_tac(tm(ab)),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(
          @list.List([
            solve(same_tac()),
            solve(seq([startup_intro_ex(), free_apply(resume_proof)])),
            solve(
              seq([
                @tactics.repeat_tac(@tactics.gen_tac),
                beta_goal(),
                @simp.rewrite_tac(
                  ths([thm("st"), thm("tlsf_malloc_start_initialized")]),
                ),
                @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                subst_vars(),
                @tactics.exists_tac(tm("(h : \{heap})")),
                @simp.asm_rewrite_tac(ths([thm("tlsf_malloc_ro")])),
              ]),
            ),
          ]),
        ),
      ]),
    )
    let pre = "st(NIL," + locals + "," + malloc_start_saved() + ")"
    let headvars = malloc_g_variables().filter(x => x.0 != "labels") +
      malloc_env_variables() +
      [
        ("L", sassn),
        ("n", w32),
        ("R", rty),
        ("l0", "Value"),
        ("l1", "Value"),
        ("l2", "Value"),
        ("l3", "Value"),
        ("l4", "Value"),
      ]
    let head = inst(
      thm("tlsf_malloc_" + v + "_start_head_all"),
      headvars.map(x => {
        if x.0 == "G" {
          startup_false_specs()
        } else if x.0 == "rp" {
          rp
        } else if x.0 == "L" {
          q
        } else if x.0 == "R" {
          malloc_start_saved()
        } else {
          "(" + x.0 + " : " + x.1 + ")"
        }
      }),
    )
    let callvars = malloc_entry_variables() +
      [
        ("d", w32),
        ("lim", "Num"),
        ("before", heap),
        ("fp", rty),
        ("l0", "Value"),
        ("l1", "Value"),
        ("rest", "List[Value]"),
      ]
    let list = @basics.dest_list(tm(locals)).to_array()
    let call = inst(
      thm("tlsf_malloc_start_ready"),
      callvars.map(x => {
        if x.0 == "l0" {
          show(list[0])
        } else if x.0 == "l1" {
          show(list[1])
        } else if x.0 == "rest" {
          show(
            @lists.mk_list(
              @list.List(list[2:].to_owned()),
              @kernel.type_of(list[0]),
            ),
          )
        } else {
          "(" + x.0 + " : " + x.1 + ")"
        }
      }),
    )
    let _ = startup_lemma(
      "tlsf_malloc_" + v + "_start_attempt",
      page_quantify(vars) +
      malloc_start_attempt_cond() +
      " → tlsf_sl_abort_r(" +
      startup_env() +
      "," +
      rp +
      "," +
      pre +
      "," +
      malloc_part(v, "body") +
      "," +
      q +
      ",[" +
      q +
      "]," +
      ab +
      ")",
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          "!(" + n + " == word(0))",
          seq([
            @simp.rewrite_tac(ths([@equal.gsym(@words.val_eq_0())])),
            @int.asm_arith_tac,
          ]),
        ),
        @simp.pure_rewrite_tac(ths([thm("tlsf_malloc_" + v + "_start_parts")])),
        @tactics.match_mp_tac(thm("tlsf_sl_abort_r_seq")),
        @tactics.exists_tac(tm(pre)),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            startup_lift_g(head),
            seq([
              @tactics.match_mp_tac(thm("tlsf_sl_abort_r_seq")),
              @tactics.exists_tac(tm(initialized)),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  seq([
                    @simp.rewrite_tac(
                      ths([
                        thm("tlsf_malloc_first_ready_guard"),
                        thm("tlsf_malloc_try_ready_guard"),
                        thm("tlsf_base"),
                      ]),
                    ),
                    startup_lift_m(
                      @simp.rewrite_rule(
                        ths([
                          thm("tlsf_malloc_try_ready_guard"),
                          thm("tlsf_base"),
                        ]),
                      )(call),
                    ),
                  ]),
                  free_apply(after),
                ]),
              ),
            ]),
          ]),
        ),
      ]),
    )
  }
}
