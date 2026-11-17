// Restore the combined invariant around each compiled small-allocation suffix.

///|
fn prove_tlsf_malloc_small_all() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let s = "(s : Num)"
  let fp = "(fp : " + rty + ")"
  let cap = "val(tlsf_size(" + a[4] + "(" + p + ")))"
  let vs = malloc_publication_variables() +
    page_model_variables() +
    [
      ("p", w),
      ("b", w),
      ("bs", lw),
      ("k", "Num"),
      ("s", "Num"),
      ("i", "Num"),
      ("used0", w),
      ("prev0", w),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
      ("fp", rty),
      ("z", lw),
    ]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let frame = block_large_frame(a, fp)
  for v in malloc_variant_names() {
    for kind in ["cached", "partial", "fresh"] {
      let cached = kind == "cached"
      let fresh = kind == "fresh"
      let size = if cached { "8*" + k } else { s }
      let n = if cached {
        malloc_cached_args(a, p, b, bs, k)
      } else {
        publish_args(a, p, b, bs, s, fresh)
      }
      let path = if cached {
        inst(
          thm("tlsf_malloc_" + v + "_cached_small"),
          malloc_publication_variables().map(x => "(" + x.0 + " : " + x.1 + ")") +
          a +
          [
            p, b, bs, k, "(i : Num)", "(l2 : Value)", "(l3 : Value)", "(l4 : Value)",
            frame,
          ],
        )
      } else {
        let args = a +
          [
            p,
            b,
            bs,
            s,
            "(i : Num)",
            "(used0 : " + w + ")",
            "(prev0 : " + w + ")",
            "(l1 : Value)",
            "(l3 : Value)",
            "(l4 : Value)",
            frame,
            "(z : " + lw + ")",
          ]
        if v == "try" {
          inst(thm("tlsf_page_publish_" + kind + "_small"), args)
        } else {
          malloc_publication_inst(
            thm("tlsf_malloc_" + v + "_publish_" + kind + "_small"),
            args,
          )
        }
      }
      let (need, body) = @basics.dest_imp(@kernel.concl(path))
      let t = args_of(body, "sl_triple", 3).unwrap()
      let oldst = args_of(t[0], "st", 3).unwrap()
      let init = "tlsf_page_allocate_build(" +
        [
          p,
          cap,
          size,
          "tlsf_small_total(" + size + ")",
          "(used0 : " + w + ")",
          "(prev0 : " + w + ")",
        ].join(",") +
        ")"
      let own = (xs : Array[String]) => {
        "(gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => ms == " +
        a[1] +
        " && " +
        small_star(
          xs + ["tlsf_allocator(" + a.join(",") + ")", "(" + fp + ")(gs,ms)"],
        ) +
        "(h)"
      }
      let pre = "st(NIL," +
        show(oldst[1]) +
        "," +
        own(if fresh { [init] } else { [] }) +
        ")"
      let post = "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => lc == " +
        malloc_suffix_locals(v, kind) +
        " && res == [" +
        malloc_i("word_add(" + b + ",word(8))") +
        "] && ms == " +
        a[1] +
        " && " +
        small_star([
          "tlsf_page_publish_payload(" + b + "," + size + ")",
          "tlsf_allocator(" + n.join(",") + ")",
          "(" + fp + ")(gs,ms)",
        ]) +
        "(h)"
      let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
      let extra = block_backing(a) +
        " && " +
        block_lists(a) +
        " && " +
        (if cached {
          physical + " && MEM(" + p + "," + a[8] + ")"
        } else if fresh {
          "MEM(" + p + "," + a[3] + ") && tlsf_used(" + a[4] + "(" + p + "))"
        } else {
          "MEM(" + p + "," + a[8] + ")"
        })
      let _ = lemma(
        "tlsf_malloc_" + v + "_" + kind + "_allocator",
        page_quantify(vs) +
        "(" +
        show(need) +
        ") && " +
        extra +
        " → sl_triple(" +
        pre +
        "," +
        show(t[1]) +
        "," +
        post +
        ")",
        seq([
          gen,
          @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
          g => {
            let model = if cached {
              inst(thm("tlsf_malloc_cached_models"), a + [p, b, bs, k])
            } else {
              inst(
                thm("tlsf_page_publish_" + kind + "_models"),
                a + [p, b, bs, s, "(z : " + lw + ")"],
              )
            }
            let model = block_under(model, g)
            let model = @simp.rewrite_rule(g.0.map(x => x.1))(model)
            @tactics.strip_assume_tac(model)(g)
          },
          @tactics.match_mp_tac(thm("sl_conseq")),
          @tactics.exists_tac(t[0]),
          @tactics.exists_tac(t[2]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              ent_tac([thm("tlsf_allocator"), thm("tlsf_small")], []),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_apply(path),
                  ent_tac([thm("tlsf_allocator"), thm("tlsf_small")], []),
                ]),
              ),
            ]),
          ),
        ]),
      )
    }
  }
  let _ = arw
}
