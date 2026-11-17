// Relate literal compiled offsets to bounded natural addresses.

///|
fn publish_geometry(
  lim : String,
  p : String,
  cap : String,
  s : String,
  b : String,
  bs : String,
  live : String,
  i : String,
) -> @tactics.Tactic raise {
  let ready = "tlsf_small_page_ok(" +
    [
      lim,
      p,
      cap,
      s,
      "CONS(" + b + "," + bs + ")",
      "(NIL : List[" + w32 + "])",
      live,
    ].join(",") +
    ")"
  seq([
    free_have(
      "8 <= " +
      s +
      " && " +
      s +
      " <= 256 && MOD(" +
      s +
      ",8) == 0 && val(" +
      p +
      ")+8+" +
      cap +
      " <= " +
      lim +
      " && " +
      lim +
      " <= 4294967296 && 1080 <= " +
      cap,
      seq([
        @tactics.undisch_tac(tm(ready)),
        @simp.rewrite_tac(ths([thm("tlsf_small_page_ok")])),
        small_meson(ths([])),
      ]),
    ),
    split_conjs(),
    g => {
      @tactics.strip_assume_tac(
        block_under(
          inst(thm("tlsf_small_slot_bounds"), [
            lim,
            p,
            cap,
            s,
            "CONS(" + b + "," + bs + ")",
            "(NIL : List[" + w32 + "])",
            live,
            i,
          ]),
          g,
        ),
      )(g)
    },
    free_have(
      "val(" + b + ")+8+" + s + " <= val(" + p + ")+8+" + cap,
      seq([
        @tactics.mp_tac(
          inst(thm("tlsf_small_slot_bounds"), [
            lim,
            p,
            cap,
            s,
            "CONS(" + b + "," + bs + ")",
            "(NIL : List[" + w32 + "])",
            live,
            i,
          ]),
        ),
        @simp.asm_rewrite_tac(ths([])),
        small_meson(ths([])),
      ]),
    ),
    seq(
      [(p, 12), (p, 16), (p, 20), (p, 24), (p, 28), (b, 8)].map(t => {
        free_have(
          "val(word_add(" +
          t.0 +
          ",(word(" +
          t.1.to_string() +
          ") : " +
          w32 +
          "))) == val(" +
          t.0 +
          ")+" +
          t.1.to_string(),
          seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
        )
      }),
    ),
  ])
}

///|
fn publish_table_word(d : String, s : String, partial : Bool) -> String {
  let base = "word_and(word_add(" + d + ",word(15)),word(4294967280))"
  if partial {
    "word_add(word_add(" + s + "," + base + "),word(1916))"
  } else {
    "word_add(" + s + ",word_add(" + base + ",word(1912)))"
  }
}

///|
fn prove_tlsf_page_publish_geometry() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  for partial in [false, true] {
    let off = if partial { 1916 } else { 1912 }
    let table = publish_table_word(
      "(d : " + w + ")",
      "(word(s) : " + w + ")",
      partial,
    )
    let _ = lemma(
      "tlsf_page_publish_" +
      (if partial { "partial" } else { "fast" }) +
      "_address",
      "∀ d : " +
      w +
      ", ∀ s : Num, val(d) <= 4294965088 && s <= 256 → val(" +
      table +
      ") == val(tlsf_base(d))+" +
      off.to_string() +
      "+s",
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          table +
          " == word_add(tlsf_base((d : " +
          w +
          ")),word(" +
          off.to_string() +
          "+(s : Num)))",
          seq([
            rw([thm("tlsf_base"), @words.word_add_v1()]),
            g => @tactics.accept_tac(@words.word_rule(g.1))(g),
          ]),
        ),
        arw([]),
        @tactics.mp_tac(
          inst(thm("tlsf_initialize_offset"), [
            "(d : " + w + ")",
            off.to_string() + "+(s : Num)",
          ]),
        ),
        free_have(off.to_string() + "+(s : Num) <= 2176", @int.asm_arith_tac),
        arw([]),
        @int.arith_tac,
      ]),
    )
  }
}
