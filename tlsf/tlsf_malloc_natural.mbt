// Kernel terms are only rewritten after proving the bounded word conversion.

///|
fn malloc_replace_term(
  t : @kernel.Term,
  old : @kernel.Term,
  new : @kernel.Term,
) -> @kernel.Term raise {
  if @basics.aconv(t, old) {
    return new
  }
  match t {
    Comb(f, x) =>
      @kernel.mk_comb(
        malloc_replace_term(f, old, new),
        malloc_replace_term(x, old, new),
      )
    Abs(v, b) => @kernel.mk_abs(v, malloc_replace_term(b, old, new))
    _ => t
  }
}

///|
fn prove_tlsf_malloc_page_natural_call() -> Unit raise {
  let a = block_model_args()
  let sn = "(sn : Num)"
  let vars = malloc_g_variables() +
    [("pop", "Num"), ("push", "Num"), ("take_idx", "Num"), ("page_idx", "Num")] +
    page_model_variables() +
    [("sn", "Num"), ("before", heap), ("fp", rty), ("caller", "List[Value]")]
  let args = vars.map(x => {
    if x.0 == "sn" {
      "(word(" + sn + ") : " + w32 + ")"
    } else {
      "(" + x.0 + " : " + x.1 + ")"
    }
  })
  let source = inst(thm("tlsf_malloc_page_call_g"), args)
  let (need, tr) = @basics.dest_imp(@kernel.concl(source))
  let t = args_of(tr, "sl_triple_g", 9).unwrap()
  let nat = malloc_replace_term(
    t[7],
    tm("val((word(" + sn + ") : " + w32 + "))"),
    tm(sn),
  )
  let _ = lemma(
    "tlsf_malloc_page_natural_call_g",
    page_quantify(vars) +
    "8 <= " +
    sn +
    " && " +
    sn +
    " <= 256 && MOD(" +
    sn +
    ",8) == 0 && (" +
    show(need) +
    ") → sl_triple_g(" +
    malloc_g_env() +
    "," +
    show(t[5]) +
    "," +
    show(t[6]) +
    "," +
    show(nat) +
    ",(labels : List[" +
    sassn +
    "]))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_have(
        "val((word(" + sn + ") : " + w32 + ")) == " + sn,
        seq([
          @simp.rewrite_tac(ths([@words.val_word(), @words.dimindex_32()])),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @tactics.match_mp_tac(@arith.mod_lt()),
          @int.asm_arith_tac,
        ]),
      ),
      g => free_apply(@simp.rewrite_rule(g.0.map(x => x.1))(source))(g),
    ]),
  )
  let _ = a
}

///|
fn malloc_orient_slot(t : @kernel.Term) -> @kernel.Thm raise {
  if args_of(t, "=", 2) is Some([Var(_, _), rhs]) &&
    head_name(rhs) == "tlsf_small_slot" {
    return @equal.sym_conv(t)
  }
  raise Failure("malloc_orient_slot")
}

///|
fn prove_tlsf_malloc_page_oriented_call() -> Unit raise {
  let source = @equal.conv_rule(
    @equal.top_depth_conv(malloc_orient_slot),
    thm("tlsf_malloc_page_natural_call_g"),
  )
  let _ = lemma(
    "tlsf_malloc_page_oriented_call_g",
    show(@kernel.concl(source)),
    @tactics.accept_tac(source),
  )
}
