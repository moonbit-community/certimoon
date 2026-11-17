// The deterministic update shared by the two allocation-side publications.

///|
fn publish_args(
  a : Array[String],
  p : String,
  b : String,
  bs : String,
  s : String,
  fresh : Bool,
) -> Array[String] {
  let r = a.copy()
  let lw = "List[" + w32 + "]"
  if fresh {
    r[8] = "CONS(" + p + "," + a[8] + ")"
    r[9] = "((q : " +
      w32 +
      ") => if q == " +
      p +
      " { " +
      s +
      " } else { " +
      a[9] +
      "(q) })"
  }
  r[10] = "tlsf_small_put(" + a[10] + "," + p + ",(NIL : " + lw + "))"
  r[11] = "tlsf_small_put(" + a[11] + "," + p + "," + bs + ")"
  r[12] = "tlsf_small_put(" +
    a[12] +
    "," +
    p +
    ",CONS(" +
    b +
    "," +
    (if fresh { "(NIL : " + lw + ")" } else { a[12] + "(" + p + ")" }) +
    "))"
  r[13] = "tlsf_small_put_class(" + a[13] + ",DIV(" + s + ",8)," + bs + ")"
  if !fresh {
    r[14] = "tlsf_small_put_class(" +
      a[14] +
      ",DIV(" +
      s +
      ",8),TL(" +
      a[14] +
      "(DIV(" +
      s +
      ",8))))"
  }
  r
}

///|
fn prove_tlsf_page_publish_partition() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let vs = "∀ p : " +
    w +
    ", ∀ s : Num, ∀ b : " +
    w +
    ", ∀ bs : " +
    lw +
    ", ∀ live : " +
    lw
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_page_publish_partition",
    vs +
    ", tlsf_small_partition(p,s,CONS(b,bs),NIL,live) → tlsf_small_partition(p,s,NIL,bs,CONS(b,live)) && tlsf_small_used(bs,CONS(b,live)) == tlsf_small_total(s)",
    seq([
      gen,
      @tactics.disch_tac,
      @tactics.mp_tac(
        inst(thm("tlsf_small_partition_export"), [
          "(p : " + w + ")",
          "(s : Num)",
          "(b : " + w + ")",
          "(bs : " + lw + ")",
          "(live : " + lw + ")",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.undisch_tac(
        tm(
          "tlsf_small_partition((p : " +
          w +
          "),(s : Num),NIL,(bs : " +
          lw +
          "),CONS((b : " +
          w +
          "),(live : " +
          lw +
          ")))",
        ),
      ),
      rw([thm("tlsf_small_partition"), @lists.length(), @arith.add_clauses()]),
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_page_publish_local_unique",
    "∀ p : " +
    w +
    ", ∀ s : Num, ∀ loc : " +
    lw +
    ", ∀ cached : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", tlsf_small_partition(p,s,loc,cached,live) && MEM(b,loc) → MEM(b,tlsf_small_slots(p,s,tlsf_small_total(s))) && tlsf_count(b,loc) == 1 && !MEM(b,live) && !MEM(b,cached)",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_have(
        "0 < tlsf_count((b : " + w + "),(loc : " + lw + "))",
        seq([rw([@equal.gsym(thm("tlsf_count_member"))]), arw([])]),
      ),
      @class.asm_cases_tac(
        tm(
          "MEM((b : " +
          w +
          "),tlsf_small_slots((p : " +
          w +
          "),(s : Num),tlsf_small_total(s)))",
        ),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_partition_counts"), [
          "(p : " + w + ")",
          "(s : Num)",
          "(loc : " + lw + ")",
          "(cached : " + lw + ")",
          "(live : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([@equal.gsym(thm("tlsf_count_zero"))]),
      @int.asm_arith_tac,
    ]),
  )
  let _ = lemma(
    "tlsf_page_publish_cached_unique",
    "∀ p : " +
    w +
    ", ∀ s : Num, ∀ loc : " +
    lw +
    ", ∀ cached : " +
    lw +
    ", ∀ live : " +
    lw +
    ", ∀ b : " +
    w +
    ", tlsf_small_partition(p,s,loc,cached,live) && MEM(b,cached) → tlsf_count(b,cached) == 1",
    seq([
      gen,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      free_have(
        "0 < tlsf_count((b : " + w + "),(cached : " + lw + "))",
        seq([rw([@equal.gsym(thm("tlsf_count_member"))]), arw([])]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_partition_counts"), [
          "(p : " + w + ")",
          "(s : Num)",
          "(loc : " + lw + ")",
          "(cached : " + lw + ")",
          "(live : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([]),
      @class.cond_cases_tac,
      @int.asm_arith_tac,
    ]),
  )
}
