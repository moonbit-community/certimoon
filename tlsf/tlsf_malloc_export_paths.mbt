// Hide the updated ghost maps after exporting a payload; keep the live handle.

///|
fn prove_tlsf_malloc_export_paths() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let k = "(k : Num)"
  let s = "(s : Num)"
  let nreq = "(nreq : " + w + ")"
  let fp = "(fp : " + rty + ")"
  let extras = [
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
  let vars = malloc_publication_variables() +
    page_model_variables() +
    extras +
    [("before", heap), ("nreq", w)]
  let args = (malloc_publication_variables() + page_model_variables() + extras).map(x => {
      "(" + x.0 + " : " + x.1 + ")"
    },
  )
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", fp]).join(",") +
    ")"
  for v in malloc_variant_names() {
    for kind in ["cached", "partial", "fresh"] {
      let cached = kind == "cached"
      let fresh = kind == "fresh"
      let size = if cached { "8*" + k } else { s }
      let newer = if cached {
        malloc_cached_args(a, p, b, bs, k)
      } else {
        publish_args(a, p, b, bs, s, fresh)
      }
      let path = inst(thm("tlsf_malloc_" + v + "_" + kind + "_allocator"), args)
      let (cond, tr) = @basics.dest_imp(@kernel.concl(path))
      let t = args_of(tr, "sl_triple", 3).unwrap()
      let lc = args_of(t[0], "st", 3).unwrap()[1]
      let pre = if fresh {
        show(t[0])
      } else {
        "st(NIL," + show(lc) + "," + r + ")"
      }
      let ptr = "word_add(" + b + ",word(8))"
      let result = "tlsf_malloc_result(" +
        a[0] +
        "," +
        nreq +
        "," +
        a[1] +
        "," +
        fp +
        "," +
        ptr +
        ")"
      let post = "(res : List[Value]) => (lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : " +
        heap +
        ") => lc == " +
        malloc_suffix_locals(v, kind) +
        " && res == [" +
        malloc_i(ptr) +
        "] && ms == " +
        a[1] +
        " && " +
        result +
        "(gs,ms,h)"
      let _ = lemma(
        "tlsf_malloc_" + v + "_" + kind + "_export",
        page_quantify(vars) +
        "(" +
        show(cond) +
        ") && val(" +
        nreq +
        ") <= " +
        size +
        " && tlsf_physical_ok(" +
        a[:5].to_owned().join(",") +
        ") → sl_triple(" +
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
            @tactics.strip_assume_tac(
              @simp.rewrite_rule(g.0.map(x => x.1))(block_under(model, g)),
            )(g)
          },
          @tactics.match_mp_tac(thm("sl_conseq")),
          @tactics.exists_tac(t[0]),
          @tactics.exists_tac(t[2]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              ent_tac([thm("tlsf_malloc_ro")], []),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_apply(path),
                  seq([
                    gen,
                    beta_goal(),
                    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
                    arw([]),
                    g => {
                      free_apply(
                        @simp.rewrite_rule(g.0.map(x => x.1))(
                          inst(
                            thm("tlsf_malloc_small_result"),
                            newer +
                            [
                              p,
                              b,
                              nreq,
                              a[1],
                              fp,
                              "(gs : List[Value])",
                              "(h : " + heap + ")",
                            ],
                          ),
                        ),
                      )(g)
                    },
                    arw([
                      thm("tlsf_small_put"),
                      @lists.mem(),
                      thm("tlsf_small_put_class"),
                    ]),
                    @tactics.first_assum(th => {
                      if head_name(@kernel.concl(th)) == "star" {
                        @tactics.undisch_tac(@kernel.concl(th))
                      } else {
                        @tactics.no_tac
                      }
                    }),
                    arw(
                      malloc_ac() +
                      [
                        thm("tlsf_small_put"),
                        thm("tlsf_small_put_class"),
                        @arith.le_refl(),
                      ],
                    ),
                  ]),
                ]),
              ),
            ]),
          ),
        ]),
      )
    }
  }
}
