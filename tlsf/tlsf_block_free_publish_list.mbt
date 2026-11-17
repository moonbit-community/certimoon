///|
fn prove_tlsf_block_free_publish_list() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let l = "(entries : \{lw})"
  let k = "DIV((s : Num),8)"
  let table = "val(tlsf_base((d : \{w})))+1916+8*\{k}"
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
    cell(table, "tlsf_small_head(" + l + ")"),
    "tlsf_small_partial_links((word(0) : " + w + ")," + l + ")",
  ])
  let post = own([
    size,
    cell(table, "p"),
    "tlsf_small_partial_links((word(0) : " +
    w +
    "),CONS((p : " +
    w +
    ")," +
    l +
    "))",
  ])
  let cond = "val((d : \{w})) <= 4294965088 && 8 <= (s : Num) && s <= 256 && MOD(s,8) == 0 && !((p : \{w}) == word(0)) && val(p)+32 <= 4294967296 && (∀ q : \{w}, MEM(q,\{l}) → !(q == word(0)) && val(q)+32 <= 4294967296)"
  let vars = "∀ entries : \{lw}, ∀ d : \{w}, ∀ free_idx : Num, ∀ p : \{w}, ∀ s : Num, ∀ u : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let simp = [thm("tlsf_small_head"), @lists.not_cons_nil(), @lists.hd()]
  let _ = lemma(
    "tlsf_block_free_publish_list",
    "\{vars}, \{cond} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_publish(d,free_idx),st([\{i("word(0)")}],[\{i("p")},\{i("tlsf_small_head("+l+")")},\{i("word("+k+")")}],\{post}))",
    () => {
      @tactics.thenl(
        @lists.list_induct_tac,
        @list.List([
          seq([
            gen,
            strip,
            rw(simp),
            free_apply(
              @simp.rewrite_rule(ths(simp))(
                thm("tlsf_block_free_publish_nil_list"),
              ),
            ),
            arw([]),
          ]),
          seq([
            gen,
            strip,
            free_have(
              "!((h : \{w}) == word(0)) && val(h)+32 <= 4294967296",
              small_meson(ths([@lists.mem()])),
            ),
            rw(simp),
            free_apply(
              @simp.rewrite_rule(ths(simp))(
                thm("tlsf_block_free_publish_cons_list"),
              ),
            ),
            arw([]),
          ]),
        ]),
      )
    },
  )
}
