///|
fn prove_tlsf_ensure_fit() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let m = "(m : \{w})"
  let hd = "(hd : \{ht})"
  let h = "\{hd}(\{m})"
  let s = "(s : \{w})"
  let p = "tlsf_ensure_pages(\{s},\{h})"
  let e = "tlsf_ensure_expected(\{s})"
  let delta = "val(\{p})*65536"
  let lim2 = "(lim : Num)+\{delta}"
  let xs = "APPEND((ys : \{lw}),[\{m}])"
  let vars = "∀ ys : \{lw}, ∀ d : \{w}, ∀ s : \{w}, ∀ lim : Num, ∀ m : \{w}, ∀ hd : \{ht}"
  let cond = "tlsf_physical_ok((d : \{w}),(lim : Num),\{m},\{xs},\{hd}) && 16 <= val(\{s}) && val(s) <= 4160749568 && DIV(lim,65536)+val(\{p}) <= 65536"
  let nt = "tlsf_grow_top(\{hd},\{m},(lim : Num))"
  let nh = "tlsf_grow_headers(\{hd},\{m},(lim : Num),\{lim2})"
  let nx = "tlsf_grow_chain(\{xs},\{hd},\{m},(lim : Num))"
  let drop_fields = @tactics.pop_assum_list(all => {
    seq(
      all
      .to_array()
      .filter(th => {
        let c = @kernel.concl(th)
        if head_name(c) == "=" {
          !["tlsf_extend_headers", "tlsf_append_headers"].contains(
            head_name(@equal.lhs(c)),
          )
        } else {
          true
        }
      })
      .map(@tactics.assume_tac),
    )
  })
  let _ = lemma(
    "tlsf_ensure_growth_fit",
    "\{vars}, \{cond} → (lim : Num) <= \{lim2} && \{lim2} <= 4294967296 && MOD(\{lim2},65536) == 0 && tlsf_physical_ok(d,\{lim2},\{nt},\{nx},\{nh}) && !tlsf_used((\{nh})(\{nt})) && val(\{e}) <= val(tlsf_size((\{nh})(\{nt})))",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_ensure_top_facts"), [
          "(ys : \{lw})",
          "(d : \{w})",
          "(lim : Num)",
          m,
          hd,
        ]),
      ),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_ensure_expected_bounds"), [s])),
      arw([]),
      strip,
      @tactics.mp_tac(inst(thm("tlsf_grow_limits"), ["(lim : Num)", p])),
      arw([]),
      strip,
      @tactics.thenl(
        @class.asm_cases_tac(tm("tlsf_used(\{h})")),
        @list.List([
          seq([
            have(
              "0 < val(\{p}) && val(\{e})+8 <= val(\{p})*65536",
              seq([
                arw([thm("tlsf_ensure_pages")]),
                @tactics.match_mp_tac(thm("tlsf_used_pages_fit")),
                arw([]),
              ]),
            ),
            @tactics.first_x_assum(th => {
              if head_name(@kernel.concl(th)) == "/\\" {
                @tactics.strip_assume_tac(th)
              } else {
                @tactics.no_tac
              }
            }),
            have("(lim : Num)+24 <= \{lim2}", @int.asm_arith_tac),
            @tactics.mp_tac(
              inst(thm("tlsf_append_model"), [
                "(ys : \{lw})",
                "(d : \{w})",
                "(lim : Num)",
                lim2,
                m,
                hd,
              ]),
            ),
            arw([]),
            strip,
            @tactics.mp_tac(
              inst(thm("tlsf_capacity_value"), [
                lim2,
                "(word((lim : Num)) : \{w})",
              ]),
            ),
            arw([]),
            have("0 < (lim : Num)", @int.asm_arith_tac),
            arw([]),
            strip,
            drop_fields,
            rw([
              thm("tlsf_grow_top"),
              thm("tlsf_grow_chain"),
              thm("tlsf_grow_headers"),
            ]),
            arw([@equal.gsym(@lists.append_assoc()), @lists.append()]),
            @int.asm_arith_tac,
          ]),
          seq([
            have(
              "val(\{e}) <= val(tlsf_size(\{h}))+val(\{p})*65536",
              seq([
                arw([thm("tlsf_ensure_pages")]),
                @tactics.match_mp_tac(thm("tlsf_free_pages_fit")),
                arw([]),
              ]),
            ),
            @tactics.mp_tac(
              inst(thm("tlsf_extend_model"), [
                "(ys : \{lw})",
                "(d : \{w})",
                "(lim : Num)",
                lim2,
                m,
                hd,
              ]),
            ),
            arw([]),
            strip,
            have("val(\{m})+24 <= \{lim2}", @int.asm_arith_tac),
            @tactics.mp_tac(inst(thm("tlsf_capacity_value"), [lim2, m])),
            arw([]),
            @tactics.disch_tac,
            drop_fields,
            rw([
              thm("tlsf_grow_top"),
              thm("tlsf_grow_chain"),
              thm("tlsf_grow_headers"),
            ]),
            arw([]),
            @int.asm_arith_tac,
          ]),
        ]),
      ),
    ]),
  )
}
