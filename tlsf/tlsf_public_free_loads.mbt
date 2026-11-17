///|
fn prove_tlsf_public_free_loads() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let fp = "(fp : " + rty + ")"
  let b = "(b : " + w + ")"
  let p = "(p : " + w + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  for small in [false, true] {
    let tag = if small { "(word(4) : " + w + ")" } else { a[4] + "(" + b + ")" }
    let cap = if small {
      a[9] + "(" + p + ")"
    } else {
      "val(tlsf_size(" + tag + "))"
    }
    let r = public_free_r(a, b, cap, fp)
    let addr = "word_sub(word_add(" + b + ",word(8)),word(8))"
    let cond = if small {
      block_backing(a) +
      " && " +
      block_lists(a) +
      " && MEM(" +
      p +
      "," +
      a[8] +
      ") && MEM(" +
      b +
      "," +
      a[12] +
      "(" +
      p +
      "))"
    } else {
      "MEM(" + b + "," + a[3] + ")"
    }
    let _ = lemma(
      "st_public_free_" + (if small { "small" } else { "large" }) + "_header",
      page_quantify(
        page_model_variables() +
        [
          ("p", w),
          ("b", w),
          ("fp", rty),
          ("v", "List[Value]"),
          ("lc", "List[Value]"),
        ],
      ) +
      cond +
      " → sl_triple(st(APPEND((v : List[Value]),[" +
      malloc_i(addr) +
      "]),(lc : List[Value])," +
      r +
      "),[Load(T_i32,NONE,2,0)],st(APPEND(v,[" +
      malloc_i(tag) +
      "]),lc," +
      r +
      "))",
      () => {
        seq([
          gen,
          strip,
          rw([thm("tlsf_public_free_unpayload")]),
          free_at(
            "public free: load rule",
            @logic.match_mp_tac(
              inst(thm("st_load_read"), [
                "(v : List[Value])", "(lc : List[Value])", r, b, tag, "2", "0",
              ]),
            ),
          ),
          gen,
          rw([@arith.add_clauses()]),
          beta_goal(),
          strip,
          free_at(
            "public free: header view",
            free_apply(
              @simp.rewrite_rule(ths([@theorems.imp_imp()]))(
                inst(
                  thm(
                    "tlsf_public_free_read_" +
                    (if small { "small" } else { "large" }),
                  ),
                  a +
                  (if small { [p, b] } else { [b] }) +
                  [
                    "star(tlsf_bytes(val(" +
                    b +
                    ")+8," +
                    cap +
                    ")," +
                    fp +
                    "((gs : List[Value]),(ms : Num)))",
                    "(h : " + heap + ")",
                  ],
                ),
              ),
            ),
          ),
          @tactics.first_x_assum(th => {
            if head_name(@kernel.concl(th)) == "star" {
              @tactics.mp_tac(th)
            } else {
              @tactics.no_tac
            }
          }),
          arw(malloc_ac()),
        ])
      },
    )
  }
}
