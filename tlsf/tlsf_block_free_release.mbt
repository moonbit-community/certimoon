///|
fn block_under(th : @kernel.Thm, g : @tactics.Goal) -> @kernel.Thm raise {
  let (a, _) = @basics.dest_imp(@kernel.concl(th))
  let fact = @bool.eqt_elim(@simp.rewrite_conv(g.0.map(p => p.1))(a))
  @bool.mp(th, fact)
}

// Lift the compiled release prefix to an entire page and an arbitrary frame.
// A formerly full page keeps its two unpublished list words separately until
// the following publish path inserts it into the partial-page list.

///|
fn prove_tlsf_block_free_release() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vs = "∀ d : \{w}, ∀ free_idx : Num, ∀ lim : Num, ∀ p : \{w}, ∀ cap : Num, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ b : \{w}, ∀ i : Num, ∀ l0 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let ok = "tlsf_small_page_ok((lim : Num),(p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) && (i : Num) < tlsf_small_total(s) && (b : \{w}) == tlsf_small_slot(p,s,i) && MEM(b,live)"
  let u = "tlsf_small_used((cached : \{lw}),(live : \{lw}))"
  let un = "tlsf_small_used((cached : \{lw}),tlsf_small_remove((b : \{w}),(live : \{lw})))"
  let old = "tlsf_small_page_heap((p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let new = "tlsf_small_page_heap((p : \{w}),(cap : Num),(s : Num),CONS((b : \{w}),(loc : \{lw})),(cached : \{lw}),tlsf_small_remove(b,(live : \{lw})))"
  let gate = "if \{u} < tlsf_small_total((s : Num)) { emp } else { tlsf_bytes(val((p : \{w}))+24,8) }"
  let frame = "tlsf_block_free_release_frame((p : \{w}),(cap : Num),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}),(b : \{w}),(i : Num))"
  let own = (q : String) => {
    "(gs : List[Value]) => (ms : Num) => star(\{q},(fp : \{rty})(gs,ms))"
  }
  let rawfp = "(gs : List[Value]) => (ms : Num) => star(\{frame},(fp : \{rty})(gs,ms))"
  let i32 = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let p = "st(NIL,[(l0 : Value),\{i32("b")},(l2 : Value)],\{own("star("+old+",tlsf_bytes(val((b : "+w+"))+8,(s : Num)))")})"
  let q = "st(NIL,[\{i32("p")},\{i32("word("+u+")")},(l2 : Value)],\{own("star("+new+","+gate+")")})"
  let args = [
    "(lim : Num)",
    "(p : " + w + ")",
    "(cap : Num)",
    "(s : Num)",
    "(loc : " + lw + ")",
    "(cached : " + lw + ")",
    "(live : " + lw + ")",
    "(b : " + w + ")",
    "(i : Num)",
  ]
  let _ = lemma(
    "tlsf_block_free_release_page",
    "\{vs}, \{ok} → sl_triple(\{p},tlsf_block_free_release(d,free_idx),\{q})",
    seq([
      gen,
      strip,
      free_have(
        "tlsf_small_partition((p : \{w}),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw})) && 8 <= s && val(p)+8+(cap : Num) <= (lim : Num) && lim <= 4294967296 && 1080 <= cap",
        seq([
          @tactics.undisch_tac(
            tm(
              "tlsf_small_page_ok((lim : Num),(p : " +
              w +
              "),(cap : Num),(s : Num),(loc : " +
              lw +
              "),(cached : " +
              lw +
              "),(live : " +
              lw +
              "))",
            ),
          ),
          rw([thm("tlsf_small_page_ok")]),
          small_meson(ths([])),
        ]),
      ),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(
              thm("tlsf_small_slot_bounds"),
              args[:7].to_owned() + ["(i : Num)"],
            ),
            g,
          ),
        )(g)
      },
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_small_release_model"), [
              "(p : " + w + ")",
              "(s : Num)",
              "(b : " + w + ")",
              "(loc : " + lw + ")",
              "(cached : " + lw + ")",
              "(live : " + lw + ")",
            ]),
            g,
          ),
        )(g)
      },
      free_have("1 <= \{u} && \{u}-1 == \{un}", @int.asm_arith_tac),
      free_have(
        "val((b : \{w}))+8+(s : Num) <= val((p : \{w}))+8+(cap : Num)",
        small_meson(ths([])),
      ),
      seq(
        [("p", 16), ("p", 20), ("b", 4), ("b", 8)].map(v => {
          free_have(
            "val(word_add((\{v.0} : \{w}),word(\{v.1}))) == val(\{v.0})+\{v.1}",
            seq([
              @tactics.match_mp_tac(thm("val_add_small")),
              @int.asm_arith_tac,
            ]),
          )
        }),
      ),
      free_have(
        "word_sub((word(\{u}) : \{w}),word(1)) == word(\{un})",
        seq([@tactics.mp_tac(inst(thm("tlsf_small_word_dec"), [u])), arw([])]),
      ),
      g => {
        let pre = block_under(
          inst(thm("tlsf_small_page_release_pre_view"), args),
          g,
        )
        let post = block_under(
          inst(thm("tlsf_small_page_release_post_view"), args),
          g,
        )
        let path = inst(thm("tlsf_block_free_release_raw"), [
          "(d : " + w + ")",
          "(free_idx : Num)",
          "(b : " + w + ")",
          "(p : " + w + ")",
          "(word(" + u + ") : " + w + ")",
          "tlsf_small_head((loc : " + lw + "))",
          "(oldword : " + w + ")",
          "(l0 : Value)",
          "(l2 : Value)",
          rawfp,
        ])
        seq([
          @tactics.conv_tac(
            @equal.rator_conv(
              @equal.rator_conv(@equal.rand_conv(@equal.subs_conv(ths([pre])))),
            ),
          ),
          @tactics.conv_tac(
            @equal.rand_conv(@equal.subs_conv(ths([@equal.gsym(post)]))),
          ),
          by_path(path, "T", [], [], [], ["(oldword : " + w + ")"]),
        ])(g)
      },
    ]),
  )
}
