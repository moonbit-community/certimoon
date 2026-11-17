// The cached path writes only the class head and the selected free link.

///|
fn prove_tlsf_malloc_cached_raw() -> Unit raise {
  let w = w32
  let i = malloc_i
  let b = "(b : " + w + ")"
  let k = "(k : " + w + ")"
  let nx = "(nx : " + w + ")"
  let pb = "word_add(" + b + ",word(8))"
  let ft = "word_add(word_add(word_and(word_add((d : " +
    w +
    "),word(15)),word(4294967280)),word(1912)),word_jshl(" +
    k +
    ",word(3)))"
  let cell = (p : String, x : String) => {
    "pts(val(" + p + "),serialise_i32(" + x + "))"
  }
  let own = (xs : Array[String]) => {
    "(gs : List[Value]) => (ms : Num) => " +
    small_star(xs + ["(fp : " + rty + ")(gs,ms)"])
  }
  let vc = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    @simp.asm_rewrite_tac(ths(malloc_ac())),
  ])
  let vars = malloc_env_variables() +
    [
      ("b", w),
      ("k", w),
      ("nx", w),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
      ("original", "Value"),
      ("fp", rty),
    ]
  for v in malloc_variant_names() {
    ignore(
      sym_prove(
        "tlsf_malloc_" + v + "_cached_raw",
        page_quantify(vars) +
        "sl_triple(st(NIL," +
        malloc_locals(v, [i(b), i(k), "l2", "l3", "l4"]) +
        "," +
        own([cell(ft, b), cell(pb, nx)]) +
        ")," +
        malloc_part(v, "cached") +
        ",st([" +
        i(pb) +
        "]," +
        malloc_locals(v, [i(pb), i(k), i(nx), "l3", "l4"]) +
        "," +
        own([cell(ft, nx), cell(pb, "(word(0) : " + w + ")")]) +
        "))",
        [],
        [vc],
        kind="lemma",
      ),
    )
  }
}
