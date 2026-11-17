// Consequences of the invariant, rather than additional assumptions about it.

///|
fn prove_tlsf_small_facts() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ps = "(ps : \{lw})"
  let sz = "(sz : (\{w}) -> Num)"
  let lo = "(loc : \{ls})"
  let ca = "(cached : \{ls})"
  let li = "(live : \{ls})"
  let fast = "(fast : (Num) -> \{lw})"
  let part = "(partial : (Num) -> \{lw})"
  let models = "\{ps},\{sz},\{lo},\{ca},\{li},\{fast},\{part}"
  let mv = "∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}"
  let _ = lemma(
    "tlsf_small_partition_counts",
    "∀ p : \{w}, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ b : \{w}, tlsf_small_partition(p,s,loc,cached,live) → tlsf_count(b,loc)+tlsf_count(b,cached)+tlsf_count(b,live) == (if MEM(b,tlsf_small_slots(p,s,tlsf_small_total(s))) { 1 } else { 0 })",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_partition"), thm("tlsf_small_count_append")]),
        strip,
        @tactics.first_x_assum(th => {
          @tactics.mp_tac(@bool.spec(tm("(b : \{w})"), th))
        }),
        @int.arith_tac,
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_slot_exact",
    "∀ p : \{w}, ∀ s : Num, ∀ loc : \{lw}, ∀ cached : \{lw}, ∀ live : \{lw}, ∀ i : Num, tlsf_small_partition(p,s,loc,cached,live) && i < tlsf_small_total(s) → tlsf_count(tlsf_small_slot(p,s,i),loc)+tlsf_count(tlsf_small_slot(p,s,i),cached)+tlsf_count(tlsf_small_slot(p,s,i),live) == 1",
    () => {
      seq([
        gen,
        strip,
        free_have(
          "MEM(tlsf_small_slot((p : \{w}),(s : Num),(i : Num)),tlsf_small_slots(p,s,tlsf_small_total(s)))",
          seq([
            rw([thm("tlsf_small_slots_member")]),
            @tactics.exists_tac(tm("(i : Num)")),
            arw([]),
          ]),
        ),
        @tactics.mp_tac(
          inst(thm("tlsf_small_partition_counts"), [
            "(p : \{w})",
            "(s : Num)",
            "(loc : \{lw})",
            "(cached : \{lw})",
            "(live : \{lw})",
            "tlsf_small_slot((p : \{w}),(s : Num),(i : Num))",
          ]),
        ),
        arw([]),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_partial_exact",
    "\{mv}, ∀ p : \{w}, tlsf_small_lists_ok(\{models}) && MEM(p,ps) && 8 <= sz(p) && sz(p) <= 256 && MOD(sz(p),8) == 0 → (MEM(p,partial(DIV(sz(p),8))) == (tlsf_small_used(cached(p),live(p)) < tlsf_small_total(sz(p)))) && (tlsf_small_used(cached(p),live(p)) < tlsf_small_total(sz(p)) → tlsf_count(p,partial(DIV(sz(p),8))) == 1)",
    () => {
      seq([
        gen,
        rw([thm("tlsf_small_lists_ok")]),
        strip,
        free_have(
          "DIV(\{sz}((p : \{w})),8) < 33",
          seq([
            @tactics.mp_tac(inst(@arith.division(), ["\{sz}((p : \{w}))", "8"])),
            @tactics.conv_tac(@calc_num.num_reduce_conv),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ),
        free_have(
          "tlsf_small_used(\{ca}((p : \{w})),\{li}(p)) < tlsf_small_total(\{sz}(p)) → tlsf_count(p,\{part}(DIV(\{sz}(p),8))) == 1",
          seq([
            @tactics.first_x_assum(th => {
              @tactics.mp_tac(@bool.spec(tm("(p : \{w})"), th))
            }),
            arw([]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        free_have(
          "MEM((p : \{w}),\{part}(DIV(\{sz}(p),8))) → tlsf_small_used(\{ca}(p),\{li}(p)) < tlsf_small_total(\{sz}(p))",
          seq([
            @tactics.first_x_assum(th => {
              @tactics.mp_tac(
                @bool.ispecl(
                  @list.List([tm("DIV(\{sz}((p : \{w})),8)"), tm("(p : \{w})")]),
                  th,
                ),
              )
            }),
            arw([]),
            @meson.meson_tac(ths([])),
          ]),
        ),
        @tactics.thenl(
          @class.asm_cases_tac(
            tm(
              "tlsf_small_used(\{ca}((p : \{w})),\{li}(p)) < tlsf_small_total(\{sz}(p))",
            ),
          ),
          @list.List([
            seq([
              free_have(
                "tlsf_count((p : \{w}),\{part}(DIV(\{sz}(p),8))) == 1",
                small_meson(ths([])),
              ),
              arw([thm("tlsf_count_member")]),
              @tactics.conv_tac(@calc_num.num_reduce_conv),
            ]),
            seq([
              free_have(
                "!MEM((p : \{w}),\{part}(DIV(\{sz}(p),8)))",
                small_meson(ths([])),
              ),
              arw([]),
            ]),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_backing_used",
    "∀ xs : \{lw}, ∀ hd : (\{w}) -> \{w}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ p : \{w}, tlsf_small_backing(xs,hd,ps,sz,loc,cached,live,lim) && MEM(p,ps) → MEM(p,xs) && tlsf_used(hd(p)) && 1080 <= val(tlsf_size(hd(p)))",
    () => {
      seq([
        rw([thm("tlsf_small_backing"), thm("tlsf_small_page_ok")]),
        @meson.meson_tac(ths([])),
      ])
    },
  )
  let _ = lemma(
    "tlsf_small_cached_exact",
    "\{mv}, ∀ p : \{w}, ∀ b : \{w}, tlsf_small_lists_ok(\{models}) && MEM(p,ps) && MEM(b,cached(p)) → tlsf_count(b,fast(DIV(sz(p),8))) == 1",
    () => seq([rw([thm("tlsf_small_lists_ok")]), @meson.meson_tac(ths([]))]),
  )
}
