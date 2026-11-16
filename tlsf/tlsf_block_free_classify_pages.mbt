// The full/non-full classifier reads only the selected page's total word.

///|
fn prove_tlsf_block_free_classify_pages() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let _ls = "(\{w}) -> \{lw}"
  let model = page_model_variables()
  let vars = page_quantify(
    model + [("p", w), ("u", w), ("l2", "Value"), ("fp", rty)],
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arg = (n : String) => {
    let v = model.filter(v => v.0 == n)[0]
    "(" + v.0 + " : " + v.1 + ")"
  }
  let args = (ns : Array[String]) => ns.map(arg)
  let pa = args(["ps", "hd", "sz", "loc", "cached", "live"])
  let geometry = args([
    "xs", "hd", "ps", "sz", "loc", "cached", "live", "lim", "fast", "partial",
  ])
  let ba = args(["xs", "hd", "ps", "sz", "loc", "cached", "live", "lim"])
  let backing = "tlsf_small_backing(" + ba.join(",") + ")"
  let s = arg("sz") + "((p : " + w + "))"
  let total = "tlsf_small_total(" + s + ")"
  let pages = "tlsf_small_pages_heap(" + pa.join(",") + ")"
  let table = "tlsf_small_table(" +
    args(["d", "fast", "partial"]).join(",") +
    ")"
  let cap = "val(tlsf_size(" + arg("hd") + "((p : " + w + "))))"
  let tail = "tlsf_block_free_page_without_total((p : " +
    w +
    ")," +
    cap +
    "," +
    s +
    "," +
    arg("loc") +
    "(p)," +
    arg("cached") +
    "(p)," +
    arg("live") +
    "(p))"
  let rest = "tlsf_small_pages_heap(tlsf_small_remove((p : " +
    w +
    ")," +
    pa[0] +
    ")," +
    pa[1:].to_owned().join(",") +
    ")"
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let frame = own([tail, rest, table])
  let all = own([pages, table])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[\{i("p")},\{i("u")},(l2 : Value)]"
  let pure = "\{backing} && MEM((p : \{w}),(ps : \{lw})) && tlsf_count(p,ps) == 1"
  let _ = lemma(
    "tlsf_block_free_classify_pages",
    "∀ free_idx : Num, \{vars} \{pure} → sl_triple(st(NIL,\{lc},\{all}),tlsf_block_free_classify(d,free_idx),st([\{i("wasm_bool((u : "+w+") == word("+total+"))")}],\{lc},\{all}))",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(
              thm("tlsf_small_page_member_geometry"),
              geometry + ["(p : " + w + ")"],
            ),
            g,
          ),
        )(g)
      },
      free_have(
        "val(word_add((p : \{w}),word(12))) == val(p)+12",
        seq([@tactics.match_mp_tac(thm("val_add_small")), @int.asm_arith_tac]),
      ),
      g => {
        let focus0 = block_under(
          inst(thm("tlsf_small_pages_focus"), pa + ["(p : " + w + ")"]),
          g,
        )
        let focus = @equal.conv_rule(
          @equal.rand_conv(
            @simp.rewrite_conv(ths([thm("tlsf_small_page_total_focus")])),
          ),
          focus0,
        )
        let path = inst(
          thm("tlsf_block_free_classify_raw"),
          args(["d"]) +
          [
            "(free_idx : Num)",
            "(p : " + w + ")",
            "(u : " + w + ")",
            "(word(" + total + ") : " + w + ")",
            "(l2 : Value)",
            frame,
          ],
        )
        let offset = @kernel.assume_rule(
          tm("val(word_add((p : " + w + "),word(12))) == val(p)+12"),
        )
        by_path(path, "T", [focus, offset], [], [focus, offset], [])(g)
      },
    ]),
  )
}
