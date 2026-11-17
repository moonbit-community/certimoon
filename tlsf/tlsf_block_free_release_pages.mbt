// Release one live slot while framing every other page and the complete
// small table. TLSF ownership and other client bytes may occupy the frame.

///|
fn prove_tlsf_block_free_release_pages() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let model = page_model_variables()
  let extras = [
    ("p", w),
    ("b", w),
    ("i", "Num"),
    ("l0", "Value"),
    ("l2", "Value"),
    ("fp", rty),
  ]
  let vars = page_quantify(model + extras)
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let _arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let cap = "val(tlsf_size((hd : (\{w}) -> \{w})((p : \{w}))))"
  let s = "(sz : (\{w}) -> Num)((p : \{w}))"
  let locp = "(loc : \{ls})((p : \{w}))"
  let cachedp = "(cached : \{ls})((p : \{w}))"
  let livep = "(live : \{ls})((p : \{w}))"
  let nloc = "tlsf_block_free_loc((loc : \{ls}),(p : \{w}),(b : \{w}))"
  let nlive = "tlsf_block_free_live((live : \{ls}),(p : \{w}),(b : \{w}))"
  let args = [
    "(ps : " + lw + ")",
    "(hd : (" + w + ") -> " + w + ")",
    "(sz : (" + w + ") -> Num)",
    "(loc : " + ls + ")",
    "(cached : " + ls + ")",
    "(live : " + ls + ")",
  ]
  let newargs = args[:3].to_owned() + [nloc, args[4], nlive]
  let old = "tlsf_small_pages_heap(" + args.join(",") + ")"
  let newer = "tlsf_small_pages_heap(" + newargs.join(",") + ")"
  let rest = "tlsf_small_pages_heap(tlsf_small_remove((p : " +
    w +
    ")," +
    args[0] +
    ")," +
    args[1:].to_owned().join(",") +
    ")"
  let table = "tlsf_small_table((d : \{w}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw}))"
  let u = "tlsf_small_used(" + cachedp + "," + livep + ")"
  let gate = "if \{u} < tlsf_small_total(\{s}) { emp } else { tlsf_bytes(val((p : \{w}))+24,8) }"
  let own = (ps : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(ps + ["(fp : " + rty + ")(gs,ms)"])
  }
  let frame = own([rest, table])
  let p0 = own([old, table, "tlsf_bytes(val((b : " + w + "))+8," + s + ")"])
  let q0 = own([newer, table, gate])
  let i32 = (v : String) => "V_num(ConstInt32((\{v} : \{w})))"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : (\{w}) -> \{w}),(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(lim : Num))"
  let lists = "tlsf_small_lists_ok((ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls}),(fast : (Num) -> \{lw}),(partial : (Num) -> \{lw}))"
  let pure = "\{backing} && \{lists} && MEM((p : \{w}),(ps : \{lw})) && MEM((b : \{w}),\{livep}) && (i : Num) < tlsf_small_total(\{s}) && b == tlsf_small_slot(p,\{s},i)"
  let _ = lemma(
    "tlsf_block_free_release_pages",
    "∀ free_idx : Num, \{vars} \{pure} → sl_triple(st(NIL,[l0,\{i32("b")},l2],\{p0}),tlsf_block_free_release(d,free_idx),st(NIL,[\{i32("p")},\{i32("word("+u+")")},l2],\{q0}))",
    () => {
      seq([
        gen,
        @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
        free_have(
          "tlsf_count((p : \{w}),(ps : \{lw})) == 1",
          seq([
            @tactics.undisch_tac(tm(lists)),
            rw([thm("tlsf_small_lists_ok")]),
            small_meson(ths([])),
          ]),
        ),
        free_have(
          "tlsf_small_page_ok((lim : Num),(p : \{w}),\{cap},\{s},\{locp},\{cachedp},\{livep})",
          seq([
            @tactics.undisch_tac(tm(backing)),
            rw([thm("tlsf_small_backing")]),
            small_meson(ths([])),
          ]),
        ),
        g => {
          let focusOld = block_under(
            inst(thm("tlsf_small_pages_focus"), args + ["(p : " + w + ")"]),
            g,
          )
          let focusNew0 = block_under(
            inst(thm("tlsf_small_pages_focus"), newargs + ["(p : " + w + ")"]),
            g,
          )
          let restEq = inst(
            thm("tlsf_small_pages_release_rest"),
            args + ["(p : " + w + ")", "(b : " + w + ")"],
          )
          let focusNew1 = @equal.conv_rule(
            @equal.rand_conv(@equal.subs_conv(ths([restEq]))),
            focusNew0,
          )
          let focusNew = @equal.conv_rule(
            @equal.rand_conv(
              @simp.rewrite_conv(
                ths([
                  thm("tlsf_block_free_loc"),
                  thm("tlsf_block_free_live"),
                  thm("tlsf_small_put"),
                ]),
              ),
            ),
            focusNew1,
          )
          let path = inst(thm("tlsf_block_free_release_page"), [
            "(d : " + w + ")",
            "(free_idx : Num)",
            "(lim : Num)",
            "(p : " + w + ")",
            cap,
            s,
            locp,
            cachedp,
            livep,
            "(b : " + w + ")",
            "(i : Num)",
            "(l0 : Value)",
            "(l2 : Value)",
            frame,
          ])
          by_path(path, "T", [focusOld], [], [focusNew], [])(g)
        },
      ])
    },
  )
}
