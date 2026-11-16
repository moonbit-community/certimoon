// The target is a live slot, so it occurs once, is absent from both free
// lists, and decreases the page's counted usage by exactly one.

///|
fn prove_tlsf_block_free_facts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ p : \{w}, ∀ s : Num, ∀ b : \{w}, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}"
  let ok = "tlsf_small_partition((p : \{w}),(s : Num),(loc : \{lw}),(cached : \{lw}),(live : \{lw}))"
  let mem = "MEM((b : \{w}),(live : \{lw}))"
  let _ = lemma(
    "tlsf_small_live_unique",
    "\{vars}, \{ok} && \{mem} → MEM(b,tlsf_small_slots(p,s,tlsf_small_total(s))) && tlsf_count(b,live) == 1 && !MEM(b,loc) && !MEM(b,cached)",
    seq([
      gen,
      strip,
      free_have(
        "0 < tlsf_count((b : \{w}),(live : \{lw}))",
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
    "tlsf_small_remove_length_one",
    "∀ xs : \{lw}, ∀ b : \{w}, tlsf_count(b,xs) == 1 → LENGTH(xs) == SUC(LENGTH(tlsf_small_remove(b,xs)))",
    seq([
      gen,
      strip,
      free_have(
        "MEM((b : \{w}),(xs : \{lw}))",
        seq([rw([thm("tlsf_count_member")]), @int.asm_arith_tac]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_member_split"), [
          "(b : " + w + ")",
          "(xs : " + lw + ")",
        ]),
      ),
      arw([]),
      strip,
      subst_vars(),
      @tactics.mp_tac(
        inst(thm("tlsf_small_count_one_split"), [
          "(a : " + lw + ")",
          "(z : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_small_remove_split"), [
          "(a : " + lw + ")",
          "(z : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      arw([@lists.length_append(), @lists.length()]),
      @int.arith_tac,
    ]),
  )
  let newlive = "tlsf_small_remove((b : \{w}),(live : \{lw}))"
  let _ = lemma(
    "tlsf_small_release_model",
    "\{vars}, \{ok} && \{mem} → tlsf_small_partition(p,s,CONS(b,loc),cached,\{newlive}) && tlsf_small_used(cached,live) == SUC(tlsf_small_used(cached,\{newlive}))",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_small_member_split"), [
          "(b : " + w + ")",
          "(live : " + lw + ")",
        ]),
      ),
      arw([]),
      strip,
      subst_vars(),
      free_have(
        "!MEM((b : \{w}),(a : \{lw})) && !MEM(b,(z : \{lw}))",
        seq([
          @tactics.match_mp_tac(thm("tlsf_small_count_one_split")),
          @tactics.mp_tac(
            inst(thm("tlsf_small_live_unique"), [
              "(p : " + w + ")",
              "(s : Num)",
              "(b : " + w + ")",
              "(loc : " + lw + ")",
              "(cached : " + lw + ")",
              "APPEND((a : " + lw + "),CONS((b : " + w + "),(z : " + lw + ")))",
            ]),
          ),
          arw([]),
          small_meson(ths([])),
        ]),
      ),
      @tactics.mp_tac(
        inst(thm("tlsf_small_remove_split"), [
          "(a : " + lw + ")",
          "(z : " + lw + ")",
          "(b : " + w + ")",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      arw([thm("tlsf_small_release_used")]),
      @tactics.match_mp_tac(thm("tlsf_small_release_partition")),
      arw([]),
    ]),
  )
}
