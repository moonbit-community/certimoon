///|
fn malloc_start_saved() -> String {
  "tlsf_initialize_saved((d : " +
  w32 +
  "),(lim : Num),(before : " +
  heap +
  "),(fp : " +
  rty +
  "))"
}

///|
fn malloc_start_initialized() -> String {
  "(gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => tlsf_initialize_post((d : " +
  w32 +
  "),(lim : Num),(before : " +
  heap +
  "),(fp : " +
  rty +
  "),NIL,gs,ms,h)"
}

///|
fn prove_tlsf_malloc_start_lookup() -> Unit raise {
  let d = "(d : " + w32 + ")"
  let lim = "(lim : Num)"
  let r = malloc_start_saved()
  let slot = "word_add(word_and(word_add(" +
    d +
    ",word(15)),word(4294967280)),word(1908))"
  let outside = "word_uge(word_jushr(" +
    slot +
    ",word(16)),(word(DIV(" +
    lim +
    ",65536)) : " +
    w32 +
    "))"
  let vars = [
    ("d", w32),
    ("lim", "Num"),
    ("before", heap),
    ("fp", rty),
    ("v", "List[Value]"),
    ("lc", "List[Value]"),
  ]
  let _ = startup_lemma(
    "st_malloc_start_load_top",
    page_quantify(vars) +
    "tlsf_initialize_valid(" +
    d +
    "," +
    lim +
    ") && !" +
    outside +
    " → sl_triple(st(APPEND((v : List[Value]),[" +
    malloc_i(slot) +
    "]),(lc : List[Value])," +
    r +
    "),[Load(T_i32,NONE,2,0)],st(APPEND(v,[" +
    malloc_i("word(0)") +
    "]),lc," +
    r +
    "))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @logic.match_mp_tac(
        inst(thm("st_load_read"), [
          "(v : List[Value])",
          "(lc : List[Value])",
          r,
          slot,
          "(word(0) : " + w32 + ")",
          "2",
          "0",
        ]),
      ),
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(
        ths([thm("tlsf_initialize_saved"), @arith.add_clauses()]),
      ),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      @simp.asm_rewrite_tac(ths([])),
      g => {
        let view = @simp.rewrite_rule(ths([thm("tlsf_base")]))(
          inst(thm("tlsf_malloc_start_zero_top"), [
            d,
            lim,
            "(fp : " + rty + ")((gs : List[Value])," + lim + ")",
            "(h : " + heap + ")",
          ]),
        )
        free_apply(@simp.rewrite_rule(g.0.map(x => x.1))(view))(g)
      },
    ]),
  )
  let _ = startup_lemma(
    "st_malloc_start_memory_size",
    page_quantify(vars) +
    "sl_triple(st((v : List[Value]),(lc : List[Value])," +
    r +
    "),[Memory_size],st(APPEND(v,[" +
    malloc_i("word(DIV(" + lim + ",65536))") +
    "]),lc," +
    r +
    "))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @logic.match_mp_tac(
        inst(thm("st_memory_size_at"), [
          "(v : List[Value])", "(lc : List[Value])", lim, r,
        ]),
      ),
      ent_tac([thm("tlsf_initialize_saved")], []),
    ]),
  )
  let args = page_arguments(malloc_env_variables())
  let params = malloc_env_variables() +
    [
      ("lim", "Num"),
      ("before", heap),
      ("fp", rty),
      ("l0", "Value"),
      ("l1", "Value"),
      ("rest", "List[Value]"),
    ]
  let locals = (x : String) => {
    "CONS((l0 : Value),CONS(" + x + ",(rest : List[Value])))"
  }
  let same = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.repeat_tac(@tactics.strip_tac),
    @tactics.rule_assum_tac(
      @simp.rewrite_rule(
        ths([
          thm("tlsf_initialize_valid"),
          thm("tlsf_initialize_saved"),
          thm("tlsf_base"),
        ]),
      ),
    ),
    split_conjs(),
    @tactics.repeat_tac(@tactics.strip_tac),
    @simp.asm_rewrite_tac(
      ths([
        thm("tlsf_initialize_saved"),
        thm("tlsf_base"),
        thm("wasm_bool_zero"),
        @wasm.thm("wasm_bool"),
        @words.word_ugt_v1(),
        @words.val_word(),
        @words.dimindex_32(),
        @arith.add1(),
      ]),
    ),
    @tactics.conv_tac(@calc_num.num_reduce_conv),
    @tactics.try_tac(@int.asm_arith_tac),
  ])
  ignore(
    sym_prove(
      "tlsf_malloc_start_guard_test_raw",
      page_quantify(params) +
      "tlsf_initialize_valid(" +
      d +
      "," +
      lim +
      ") && !word_ugt(" +
      d +
      ",word(4294965088)) → sl_triple(st(NIL," +
      locals("(l1 : Value)") +
      "," +
      r +
      "),tlsf_malloc_start_guard_test(" +
      args +
      "),st([" +
      malloc_i("word(1)") +
      "]," +
      locals(malloc_i(slot)) +
      "," +
      r +
      "))",
      [],
      () => Array::make(5, same),
      afters=[
        "st(NIL," + locals(malloc_i(d)) + "," + r + ")",
        "st([" +
        malloc_i("word(0)") +
        "]," +
        locals(malloc_i(slot)) +
        "," +
        r +
        ")",
      ],
      rules=step_rules +
        ["st_malloc_start_load_top", "st_malloc_start_memory_size"],
      rws=[
        thm("tlsf_base"),
        thm("tlsf_initialize_valid"),
        thm("wasm_bool_zero"),
        @wasm.thm("wasm_bool"),
      ],
      kind="lemma",
    ),
  )
}
