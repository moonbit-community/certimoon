///|
fn malloc_false() -> String {
  "((vs : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => F)"
}

///|
fn malloc_program_code(code : String) -> @kernel.Term raise {
  let t = tm(code)
  let name = head_name(t)
  @equal.rhs(@kernel.concl(@simp.rewrite_conv(ths([thm(name)]))(t)))
}

///|
fn malloc_continuations(code : @kernel.Term) -> Array[@kernel.Term] raise {
  let out = []
  fn walk(t : @kernel.Term) -> Unit raise {
    if !@basics.is_list(t) {
      return
    }
    let instructions = @basics.dest_list(t).to_array()
    for k, instr in instructions {
      let name = head_name(instr)
      let args = @basics.strip_comb(instr).1.to_array()
      if k + 1 < instructions.length() && ["Block", "If", "Loop"].contains(name) {
        out.push(instr)
      }
      match name {
        "Block" | "Loop" => walk(args[1])
        "If" => {
          walk(args[1])
          walk(args[2])
        }
        _ => ()
      }
    }
  }
  walk(code)
  out
}

///|
fn malloc_guard_cond(a : Array[String]) -> String {
  let slot = "word_add(word_and(word_add(" +
    a[0] +
    ",word(15)),word(4294967280)),word(1908))"
  "!word_ugt(" +
  a[0] +
  ",word(4294965088)) && !word_uge(word_jushr(" +
  slot +
  ",word(16)),(word(DIV(" +
  a[1] +
  ",65536)) : " +
  w32 +
  ")) && !(" +
  a[2] +
  " == word(0))"
}

///|
fn malloc_helper_natives() -> String raise {
  let a = block_model_args()
  let args = [
      "(fs : List[Cl])",
      "(tabs : List[(Tab_t,List[V_ref])])",
      "(inst : Inst)",
      a[0],
      "(pop : Num)",
      "(push : Num)",
      "(take_idx : Num)",
      "(page_idx : Num)",
    ] +
    a[1:].to_owned() +
    [
      "(word(8) : " + w32 + ")",
      "(before : " + heap + ")",
      "(fp : " + rty + ")",
      "(NIL : List[Value])",
      "(NIL : List[Value])",
    ]
  show(
    @basics.dest_imp(@kernel.concl(inst(thm("tlsf_malloc_page_all"), args))).0,
  )
}

///|
fn prove_tlsf_malloc_guard_facts() -> Unit raise {
  let a = block_model_args()
  let _ = lemma(
    "tlsf_malloc_guard_facts",
    page_quantify(page_model_variables()) +
    "tlsf_physical_ok(" +
    a[:5].to_owned().join(",") +
    ") → " +
    malloc_guard_cond(a),
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @tactics.disch_tac,
        g => {
          @tactics.strip_assume_tac(
            @simp.rewrite_rule(ths([thm("tlsf_base")]))(
              block_under(inst(thm("tlsf_malloc_initialized_guards"), a), g),
            ),
          )(g)
        },
        @simp.asm_rewrite_tac(
          ths([
            thm("tlsf_base"),
            @words.word_ugt_v1(),
            @words.val_word(),
            @words.dimindex_32(),
          ]),
        ),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        @int.asm_arith_tac,
      ])
    },
  )
}

///|
fn prove_tlsf_malloc_dead_parts() -> Unit raise {
  let vars = malloc_g_variables() + malloc_env_variables() + [("P", sassn)]
  for v in malloc_variant_names() {
    for part in ["small", "large"] {
      let _ = lemma(
        "tlsf_malloc_" + v + "_dead_" + part,
        page_quantify(vars) +
        "F → sl_triple_g(" +
        malloc_g_env() +
        ",(P : " +
        sassn +
        ")," +
        malloc_part(v, part) +
        "," +
        malloc_false() +
        ",(labels : List[" +
        sassn +
        "]))",
        () => {
          seq([@tactics.repeat_tac(@tactics.strip_tac), small_meson(ths([]))])
        },
      )
    }
  }
}

///|
fn malloc_attempt_post(v : String, a : Array[String], n : String) -> String {
  let post = "tlsf_try_malloc_post(" +
    (a + [n, "(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  if v == "try" {
    return body_post(post)
  }
  let work = ["out0", "out1", "out2", "out3", "out4"]
  let locals_for = malloc_locals(v, work.map(x => "(" + x + " : Value)"))
  let locals_for = if v == "first" {
    locals_for.replace(old="(original : Value)", new=malloc_i(n))
  } else {
    locals_for
  }
  "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
  heap +
  ") => " +
  work.map(x => "∃ " + x + " : Value, ").join("") +
  "lc == " +
  locals_for +
  " && " +
  post +
  "(res,gs,ms,h)"
}

///|
fn malloc_code_prefix(prefix : @kernel.Term, code : @kernel.Term) -> Bool raise {
  let p = @basics.dest_list(prefix).to_array()
  let c = @basics.dest_list(code).to_array()
  p.length() <= c.length() && p.mapi((k, x) => x == c[k]).all(x => x)
}
