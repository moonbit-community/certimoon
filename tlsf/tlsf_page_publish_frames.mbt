// Publication changes one page's ghost maps and one small-table class.
// All remaining pages and table entries keep their exact heap predicates.

///|
fn prove_tlsf_page_publish_frames() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let s = "(s : Num)"
  let vs = page_model_variables() +
    [("p", w), ("b", w), ("bs", lw), ("s", "Num")]
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  for fresh in [false, true] {
    let n = publish_args(a, p, b, bs, s, fresh)
    let oldrest = a.copy()
    let newrest = n.copy()
    oldrest[8] = if fresh {
      a[8]
    } else {
      "tlsf_small_remove(" + p + "," + a[8] + ")"
    }
    newrest[8] = oldrest[8]
    let _ = lemma(
      "tlsf_page_publish_" +
      (if fresh { "fresh" } else { "partial" }) +
      "_pages_rest",
      page_quantify(vs) +
      (if fresh { "!MEM(" + p + "," + a[8] + ") → " } else { "" }) +
      block_pages(newrest) +
      " == " +
      block_pages(oldrest),
      () => {
        seq([
          gen,
          if fresh {
            @tactics.disch_tac
          } else {
            @tactics.all_tac
          },
          rw([thm("tlsf_small_pages_hlist")]),
          @logic.match_mp_tac(thm("tlsf_small_hlist_cong")),
          @tactics.x_gen_tac(tm("(q : " + w + ")")),
          @tactics.disch_tac,
          free_have(
            "!((q : " + w + ") == " + p + ")",
            small_meson(ths([thm("tlsf_small_remove_member")])),
          ),
          rw([thm("tlsf_small_put")]),
          arw([]),
        ])
      },
    )
  }
  let d = a[0]
  let fast = a[13]
  let part = a[14]
  let nf = "tlsf_small_put_class(" + fast + ",(k : Num)," + bs + ")"
  let np = "tlsf_small_put_class(" + part + ",(k : Num),(z : " + lw + "))"
  let rest = (f : String, t : String) => {
    "tlsf_istar((j : Num) => if j == (k : Num) { emp } else { tlsf_small_table_item(" +
    d +
    "," +
    f +
    "," +
    t +
    ",j) },33)"
  }
  let _ = lemma(
    "tlsf_page_publish_table_rest",
    page_quantify(vs + [("k", "Num"), ("z", lw)]) +
    rest(nf, np) +
    " == " +
    rest(fast, part),
    () => {
      seq([
        gen,
        @logic.match_mp_tac(thm("tlsf_istar_cong")),
        @tactics.x_gen_tac(tm("(j : Num)")),
        @tactics.disch_tac,
        @class.asm_cases_tac(tm("(j : Num) == (k : Num)")),
        arw([]),
        rw([thm("tlsf_small_table_item"), thm("tlsf_small_put_class")]),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_page_publish_put_class_same",
    "∀ ff : (Num) -> " +
    lw +
    ", ∀ k : Num, tlsf_small_put_class(ff,k,ff(k)) == ff",
    () => {
      seq([
        gen,
        rw([@class.fun_eq_thm(), thm("tlsf_small_put_class")]),
        gen,
        @class.cond_cases_tac,
        arw([]),
      ])
    },
  )
}
