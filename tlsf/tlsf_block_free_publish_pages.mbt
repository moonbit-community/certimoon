// Publishing changes only the table's list ownership. All slot payloads and
// the remaining page heaps stay framed, including their live client bytes.

///|
fn prove_tlsf_block_free_publish_pages() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let _ls = "(\{w}) -> \{lw}"
  let model = page_model_variables()
  let vars = page_quantify(
    model + [("p", w), ("u", "Value"), ("l2", "Value"), ("fp", rty)],
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let _rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
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
  let k = "DIV(" + s + ",8)"
  let old = "tlsf_small_pages_heap(" + pa.join(",") + ")"
  let table = "tlsf_small_table(" +
    args(["d", "fast", "partial"]).join(",") +
    ")"
  let newer = "tlsf_small_put_class(" +
    arg("partial") +
    "," +
    k +
    ",CONS((p : " +
    w +
    ")," +
    arg("partial") +
    "(" +
    k +
    ")))"
  let table2 = "tlsf_small_table(" +
    args(["d", "fast"]).join(",") +
    "," +
    newer +
    ")"
  let cap = "val(tlsf_size(" + arg("hd") + "((p : " + w + "))))"
  let tail = "tlsf_block_free_page_tail((p : " +
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
  let frame = own([tail, rest])
  let pre = own([old, table, "tlsf_bytes(val((p : " + w + "))+24,8)"])
  let post = own([old, table2])
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let pure = "\{backing} && MEM((p : \{w}),(ps : \{lw})) && tlsf_count(p,ps) == 1 && val((d : \{w})) <= 4294965088 && (∀ q : \{w}, MEM(q,(partial : (Num) -> \{lw})(\{k})) → !(q == word(0)) && val(q)+32 <= 4294967296)"
  let _ = lemma(
    "tlsf_block_free_publish_pages",
    "∀ free_idx : Num, \{vars} \{pure} → sl_triple(st(NIL,[\{i("p")},u,l2],\{pre}),tlsf_block_free_publish(d,free_idx),st([\{i("word(0)")}],[\{i("p")},\{i("tlsf_small_head("+arg("partial")+"("+k+"))")},\{i("word("+k+")")}],\{post}))",
    () => {
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
        g => {
          let focus0 = block_under(
            inst(thm("tlsf_small_pages_focus"), pa + ["(p : " + w + ")"]),
            g,
          )
          let focus = @equal.conv_rule(
            @equal.rand_conv(
              @simp.rewrite_conv(ths([thm("tlsf_small_page_size_focus")])),
            ),
            focus0,
          )
          let path = inst(
            thm("tlsf_block_free_publish_table"),
            args(["d"]) +
            ["(free_idx : Num)"] +
            args(["fast", "partial"]) +
            ["(p : " + w + ")", s, "(u : Value)", "(l2 : Value)", frame],
          )
          by_path(path, "T", [focus], [], [focus], [])(g)
        },
      ])
    },
  )
}
