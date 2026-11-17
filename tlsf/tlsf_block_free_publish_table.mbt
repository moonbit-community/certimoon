// Insert a newly partial page into the correct class of the entire table.

///|
fn prove_tlsf_block_free_publish_table() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let k = "DIV((s : Num),8)"
  let old = "(partial : (Num) -> \{lw})"
  let entries = "\{old}(\{k})"
  let newer = "tlsf_small_put_class(\{old},\{k},CONS((p : \{w}),\{entries}))"
  let fast = "(fast : (Num) -> \{lw})"
  let rest = "tlsf_istar((j : Num) => if j == \{k} { emp } else { tlsf_small_table_item((d : \{w}),\{fast},\{old},j) },33)"
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let cell = (a : String, v : String) => {
    "pts(\{a},serialise_i32((\{v} : \{w})))"
  }
  let size = cell("val((p : " + w + "))+8", "word((s : Num))")
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let pre = own([
    size,
    "tlsf_bytes(val((p : " + w + "))+24,8)",
    "tlsf_small_table((d : " + w + ")," + fast + "," + old + ")",
  ])
  let post = own([
    size,
    "tlsf_small_table((d : " + w + ")," + fast + "," + newer + ")",
  ])
  let frame = own([
    rest,
    cell(
      "val(tlsf_base((d : " + w + ")))+1912+8*" + k,
      "tlsf_small_head(" + fast + "(" + k + "))",
    ),
    "tlsf_small_links(" + fast + "(" + k + "))",
  ])
  let cond = "val((d : \{w})) <= 4294965088 && 8 <= (s : Num) && s <= 256 && MOD(s,8) == 0 && !((p : \{w}) == word(0)) && val(p)+32 <= 4294967296 && (∀ q : \{w}, MEM(q,\{entries}) → !(q == word(0)) && val(q)+32 <= 4294967296)"
  let vars = "∀ d : \{w}, ∀ free_idx : Num, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ p : \{w}, ∀ s : Num, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let _ = lemma(
    "tlsf_block_free_publish_table",
    "\{vars}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_publish(d,free_idx),st([\{i("word(0)")}],[\{i("p")},\{i("tlsf_small_head("+entries+")")},\{i("word("+k+")")}],\{post}))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        g => {
          @tactics.strip_assume_tac(
            block_under(inst(thm("tlsf_small_class_bounds"), ["(s : Num)"]), g),
          )(g)
        },
        g => {
          let focusOld = block_under(
            inst(thm("tlsf_small_table_focus"), [
              "(d : " + w + ")",
              fast,
              old,
              k,
            ]),
            g,
          )
          let focusNew = block_under(
            inst(thm("tlsf_small_table_focus"), [
              "(d : " + w + ")",
              fast,
              newer,
              k,
            ]),
            g,
          )
          let restNew = inst(thm("tlsf_small_table_update_rest"), [
            "(d : " + w + ")",
            fast,
            old,
            k,
            "CONS((p : " + w + ")," + entries + ")",
          ])
          let path = inst(thm("tlsf_block_free_publish_list"), [
            entries,
            "(d : " + w + ")",
            "(free_idx : Num)",
            "(p : " + w + ")",
            "(s : Num)",
            "(u : Value)",
            "(l2 : Value)",
            frame,
          ])
          by_path(
            path,
            "T",
            [focusOld, thm("tlsf_small_table_item")],
            [],
            [
              focusNew,
              restNew,
              thm("tlsf_small_table_item"),
              thm("tlsf_small_put_class"),
              thm("tlsf_small_head"),
              @lists.not_cons_nil(),
              @lists.hd(),
            ],
            [],
          )(g)
        },
      ])
    },
  )
}
