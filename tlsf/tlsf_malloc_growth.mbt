// Growth may change the last flag, while every old used payload keeps its size.

///|
fn prove_tlsf_malloc_growth_retains() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let p = "(p : " + w + ")"
  let physical = "tlsf_physical_ok(" + a[:5].to_owned().join(",") + ")"
  let lay = "tlsf_layout(word(0),tlsf_origin(" +
    a[0] +
    ")," +
    a[1] +
    "," +
    a[2] +
    "," +
    a[3] +
    "," +
    a[4] +
    ")"
  let nh = "tlsf_grow_headers(" +
    a[4] +
    "," +
    a[2] +
    "," +
    a[1] +
    ",(lim2 : Num))"
  let nx = "tlsf_grow_chain(" +
    a[3] +
    "," +
    a[4] +
    "," +
    a[2] +
    "," +
    a[1] +
    ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_malloc_backing_used",
    page_quantify(page_model_variables() + [("p", w)]) +
    block_backing(a) +
    " && MEM(" +
    p +
    "," +
    a[8] +
    ") → MEM(" +
    p +
    "," +
    a[3] +
    ") && tlsf_used(" +
    a[4] +
    "(" +
    p +
    "))",
    seq([rw([thm("tlsf_small_backing")]), small_meson(ths([]))]),
  )
  let _ = lemma(
    "tlsf_malloc_growth_retains",
    page_quantify(page_model_variables() + [("p", w), ("lim2", "Num")]) +
    physical +
    " && MEM(" +
    p +
    "," +
    a[3] +
    ") && tlsf_used(" +
    a[4] +
    "(" +
    p +
    ")) → MEM(" +
    p +
    "," +
    nx +
    ") && tlsf_used((" +
    nh +
    ")(" +
    p +
    ")) && tlsf_size((" +
    nh +
    ")(" +
    p +
    ")) == tlsf_size(" +
    a[4] +
    "(" +
    p +
    "))",
    seq([
      gen,
      strip,
      free_have(
        lay + " && " + a[1] + " <= 4294967296",
        seq([
          @tactics.undisch_tac(tm(physical)),
          rw([thm("tlsf_physical_ok")]),
          page_publish_atomic([]),
        ]),
      ),
      split_conjs(),
      g => {
        @tactics.assume_tac(
          block_under(
            inst(thm("tlsf_layout_members"), [
              a[3],
              "(word(0) : " + w + ")",
              "tlsf_origin(" + a[0] + ")",
              a[1],
              a[2],
              a[4],
              p,
            ]),
            g,
          ),
        )(g)
      },
      free_have(
        "0 < val(" + p + ") && val(" + p + ") < " + a[1],
        seq([
          @tactics.undisch_tac(
            tm(
              "tlsf_block_ok(val(" +
              p +
              ")," +
              a[1] +
              "," +
              p +
              "," +
              a[4] +
              ")",
            ),
          ),
          rw([thm("tlsf_block_ok"), @equal.gsym(@words.val_eq_0())]),
          strip,
          @int.asm_arith_tac,
        ]),
      ),
      split_conjs(),
      free_have(
        "!(" + p + " == (word(" + a[1] + ") : " + w + "))",
        seq([
          @tactics.thenl(
            @class.asm_cases_tac(tm(a[1] + " < 4294967296")),
            @list.List([
              seq([
                rw([
                  @equal.gsym(@words.val_eq()),
                  @words.val_word(),
                  @words.dimindex_32(),
                ]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
                @simp.asm_simp_tac(ths([@arith.mod_lt()])),
                @int.asm_arith_tac,
              ]),
              seq([
                free_have(a[1] + " == 4294967296", @int.asm_arith_tac),
                arw([
                  @equal.gsym(@words.val_eq()),
                  @words.val_word(),
                  @words.dimindex_32(),
                ]),
                @tactics.conv_tac(@calc_num.num_reduce_conv),
                @int.asm_arith_tac,
              ]),
            ]),
          ),
        ]),
      ),
      rw([thm("tlsf_grow_headers"), thm("tlsf_grow_chain")]),
      @class.cond_cases_tac,
      arw([
        thm("tlsf_append_headers"),
        thm("tlsf_extend_headers"),
        thm("tlsf_put"),
        @lists.mem_append(),
        @theorems.eq_sym_eq(),
      ]),
      @tactics.thenl(
        @class.asm_cases_tac(tm(p + " == " + a[2])),
        @list.List([
          seq([
            subst_vars(),
            arw([thm("tlsf_clear_last_fields")]),
            @tactics.try_tac(page_publish_atomic([])),
          ]),
          arw([]),
        ]),
      ),
    ]),
  )
}
