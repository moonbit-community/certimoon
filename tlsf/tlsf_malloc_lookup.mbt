///|
fn define_tlsf_malloc_ro() -> Unit raise {
  let a = block_model_args()
  def(
    "tlsf_malloc_ro",
    "tlsf_malloc_ro(" +
    a.join(",") +
    ",(before : " +
    heap +
    "),(fp : " +
    rty +
    ")) == (" +
    malloc_frame(a, "(fp : " + rty + ")", "(before : " + heap + ")") +
    ")",
  )
}

///|
fn prove_tlsf_malloc_table_addresses() -> Unit raise {
  let w = w32
  let d = "(d : " + w + ")"
  let kw = "(kw : " + w + ")"
  let base = "word_and(word_add(" + d + ",word(15)),word(4294967280))"
  let sh = "word_jshl(" + kw + ",word(3))"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  for fast in [true, false] {
    let off = if fast { "1912" } else { "1916" }
    let addr = if fast {
      "word_add(word_add(" + base + ",word(1912))," + sh + ")"
    } else {
      "word_add(word_add(" + sh + "," + base + "),word(1916))"
    }
    let _ = lemma(
      "tlsf_malloc_" + (if fast { "fast" } else { "partial" }) + "_word_address",
      "∀ d : " +
      w +
      ", ∀ kw : " +
      w +
      ", val(d) <= 4294965088 && val(kw) < 33 → val(" +
      addr +
      ") == val(tlsf_base(d))+" +
      off +
      "+8*val(kw)",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            let shift = block_under(
              inst(thm("tlsf_malloc_small_shift"), ["val(" + kw + ")"]),
              g,
            )
            let shift = @simp.rewrite_rule(ths([@words.word_val()]))(shift)
            @tactics.assume_tac(shift)(g)
          },
          free_have(
            addr +
            " == word_add(tlsf_base(" +
            d +
            "),word(" +
            off +
            "+8*val(" +
            kw +
            ")))",
            seq([
              arw([thm("tlsf_base"), @words.word_add_v1()]),
              g => @tactics.accept_tac(@words.word_rule(g.1))(g),
            ]),
          ),
          arw([]),
          @tactics.mp_tac(
            inst(thm("tlsf_initialize_offset"), [d, off + "+8*val(" + kw + ")"]),
          ),
          free_have(off + "+8*val(" + kw + ") <= 2176", @int.asm_arith_tac),
          arw([]),
          @int.arith_tac,
        ])
      },
    )
  }
}

///|
fn prove_tlsf_malloc_loads() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let model = page_model_variables()
  let d = a[0]
  let kw = "(kw : " + w + ")"
  let base = "word_and(word_add(" + d + ",word(15)),word(4294967280))"
  let sh = "word_jshl(" + kw + ",word(3))"
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  for kind in ["fast", "partial", "top"] {
    let fast = kind == "fast"
    let top = kind == "top"
    let addr = if top {
      "word_add(" + base + ",word(1908))"
    } else if fast {
      "word_add(word_add(" + base + ",word(1912))," + sh + ")"
    } else {
      "word_add(word_add(" + sh + "," + base + "),word(1916))"
    }
    let value = if top {
      a[2]
    } else {
      "tlsf_small_head(" + a[if fast { 13 } else { 14 }] + "(val(" + kw + ")))"
    }
    let vars = model +
      [
        ("before", heap),
        ("fp", rty),
        ("kw", w),
        ("v", "List[Value]"),
        ("lc", "List[Value]"),
      ]
    let cond = if top {
      "T"
    } else {
      "val(" + d + ") <= 4294965088 && val(" + kw + ") < 33"
    }
    let _ = lemma(
      "st_malloc_load_" + kind,
      page_quantify(vars) +
      cond +
      " → sl_triple(st(APPEND((v : List[Value]),[" +
      malloc_i(addr) +
      "]),(lc : List[Value])," +
      r +
      "),[Load(T_i32,NONE,2,0)],st(APPEND(v,[" +
      malloc_i(value) +
      "]),lc," +
      r +
      "))",
      () => {
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          @logic.match_mp_tac(
            inst(thm("st_load_read"), [
              "(v : List[Value])", "(lc : List[Value])", r, addr, value, "2", "0",
            ]),
          ),
          if top {
            @tactics.all_tac
          } else {
            g => {
              @tactics.assume_tac(
                block_under(
                  inst(thm("tlsf_malloc_" + kind + "_word_address"), [d, kw]),
                  g,
                ),
              )(g)
            }
          },
          gen,
          rw([thm("tlsf_malloc_ro"), @arith.add_clauses()]),
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          if top {
            seq([rw([@equal.gsym(thm("tlsf_base"))]), arw([])])
          } else {
            arw([])
          },
          g => {
            let view = inst(
              thm("tlsf_malloc_read_" + kind),
              a +
              (if top { [] } else { ["val(" + kw + ")"] }) +
              [
                "(fp : " + rty + ")((gs : List[Value])," + a[1] + ")",
                "(h : " + heap + ")",
              ],
            )
            let view = @simp.rewrite_rule(g.0.map(x => x.1))(view)
            free_apply(view)(g)
          },
        ])
      },
    )
  }
}

///|
fn prove_tlsf_malloc_memory_size() -> Unit raise {
  let a = block_model_args()
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let _ = lemma(
    "st_malloc_memory_size",
    page_quantify(
      page_model_variables() +
      [
        ("before", heap),
        ("fp", rty),
        ("v", "List[Value]"),
        ("lc0", "List[Value]"),
      ],
    ) +
    "sl_triple(st((v : List[Value]),(lc0 : List[Value])," +
    r +
    "),[Memory_size],st(APPEND(v,[" +
    malloc_i("word(DIV(" + a[1] + ",65536))") +
    "]),lc0," +
    r +
    "))",
    () => {
      seq([
        @tactics.repeat_tac(@tactics.gen_tac),
        @logic.match_mp_tac(
          inst(thm("st_memory_size_at"), [
            "(v : List[Value])",
            "(lc0 : List[Value])",
            a[1],
            r,
          ]),
        ),
        ent_tac([thm("tlsf_malloc_ro")], []),
      ])
    },
  )
}
