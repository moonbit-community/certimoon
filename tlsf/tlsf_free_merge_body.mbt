// Compose argument evaluation, the real native pop, and the merge stores.

///|
fn prove_tlsf_free_merge_body() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let ft = "(List[Value],List[Value],Num,\{heap}) -> Bool"
  let gt = "(Num,\{ft},\{ft}) -> Bool"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let hd = "(hd : \{ht})"
  let m = "(m : \{w})"
  let r = "(r : \{w})"
  let vars = "∀ G : \{gt}, ∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ rp : \{sassn}, ∀ labels : List[\{sassn}], ∀ ys : \{lw}, ∀ n : \{w}, ∀ ts : \{lw}, ∀ m : \{w}, ∀ r : \{w}, ∀ d : \{w}, ∀ pop : Num, ∀ push : Num, ∀ lim : Num, ∀ top : \{w}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ us : \{lw}, ∀ vs : \{lw}, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let native = "EL(sfunc_ind((inst : Inst),(pop : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code((d : \{w})))"
  for prev in [true, false] {
    let active = if prev { r } else { m }
    let other = if prev { m } else { r }
    let h = "\{hd}(\{other})"
    let removed = "APPEND((us : \{lw}),(vs : \{lw}))"
    let nfl = "tlsf_pop_fl(\{h},(fl : \{w}),(sb : (Num) -> \{w}),\{removed})"
    let nsb = "tlsf_pop_sb(\{h},(sb : (Num) -> \{w}),\{removed})"
    let nbl = "tlsf_pop_bl(\{h},(bl : \{bt}),\{removed})"
    let lc1 = "[\{i(active)},\{i(other)},(l2 : Value)]"
    for last in [true, false] {
      let suffix = if last {
        "(NIL : \{lw})"
      } else {
        "CONS((n : \{w}),(ts : \{lw}))"
      }
      let xs = "APPEND((ys : \{lw}),CONS(\{m},CONS(\{r},\{suffix})))"
      let cond = "\{native} && tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active}) && !tlsf_used(\{hd}(\{m})) && !tlsf_used(\{hd}(\{r})) && tlsf_bins_match(\{xs},tlsf_mark(\{hd},\{active}),(bl : \{bt})) && (bl : \{bt})(tlsf_level_of(\{h}))(tlsf_slot_of(\{h})) == APPEND((us : \{lw}),CONS(\{other},(vs : \{lw})))"
      let arg = @simp.rewrite_rule(ths([@class.eta_ax()]))(
        inst(
          thm(
            if prev {
              "tlsf_free_prev_arg_state"
            } else {
              "tlsf_free_next_arg_state"
            },
          ),
          [
            "(ys : \{lw})",
            suffix,
            m,
            r,
            "(d : \{w})",
            "(pop : Num)",
            "(push : Num)",
            "(lim : Num)",
            "(top : \{w})",
            hd,
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(l1 : Value)",
            "(l2 : Value)",
            "(fp : \{rty})",
          ],
        ),
      )
      let ap = args_of(@basics.dest_imp(@kernel.concl(arg)).1, "sl_triple", 3).unwrap()
      let popth = @simp.rewrite_rule(ths([@class.eta_ax()]))(
        inst(
          thm(
            if prev {
              "tlsf_free_pop_prev_pair"
            } else {
              "tlsf_free_pop_next_pair"
            },
          ),
          [
            "(fs : List[Cl])",
            "(tabs : List[(Tab_t,List[V_ref])])",
            "(inst : Inst)",
            "(d : \{w})",
            "(pop : Num)",
            "(ys : \{lw})",
            suffix,
            m,
            r,
            "(lim : Num)",
            "(top : \{w})",
            hd,
            "(fl : \{w})",
            "(sb : (Num) -> \{w})",
            "(bl : \{bt})",
            "(us : \{lw})",
            "(vs : \{lw})",
            lc1,
            "(fp : \{rty})",
          ],
        ),
      )
      let pp = args_of(
        @basics.dest_imp(@kernel.concl(popth)).1,
        "sl_triple_m",
        7,
      ).unwrap()
      let write = @simp.rewrite_rule(ths([@class.eta_ax()]))(
        inst(
          thm(
            "tlsf_free_merge_" +
            (if prev { "prev" } else { "next" }) +
            (if last { "_last" } else { "_interior" }),
          ),
          [
            "(ys : \{lw})",
            "(n : \{w})",
            "(ts : \{lw})",
            m,
            r,
            "(d : \{w})",
            "(pop : Num)",
            "(push : Num)",
            "(lim : Num)",
            "(top : \{w})",
            hd,
            nfl,
            nsb,
            nbl,
            "(l2 : Value)",
            "(fp : \{rty})",
          ],
        ),
      )
      let wp = args_of(@basics.dest_imp(@kernel.concl(write)).1, "sl_triple", 3).unwrap()
      let _ = lemma(
        "tlsf_free_merge_" +
        (if prev { "prev" } else { "next" }) +
        (if last { "_last_body" } else { "_interior_body" }),
        "\{vars}, \{cond} → sl_triple_g(G,fs,tabs,inst,rp,\{show(ap[0])},tlsf_free_" +
        (if prev { "prev" } else { "next" }) +
        "_body(d,pop,push),\{show(wp[2])},labels)",
        seq([
          gen,
          strip,
          @tactics.mp_tac(
            inst(thm("tlsf_free_pair_facts"), [
              "(ys : \{lw})",
              suffix,
              m,
              r,
              "(word(0) : \{w})",
              "tlsf_origin((d : \{w}))",
              "(lim : Num)",
              "(top : \{w})",
              hd,
            ]),
          ),
          @tactics.mp_tac(
            @simp.rewrite_rule(ths([thm("tlsf_free_geom_facts")]))(
              @kernel.assume_rule(
                tm(
                  "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},\{hd},\{active})",
                ),
              ),
            ),
          ),
          strip,
          arw([]),
          strip,
          @tactics.mp_tac(
            inst(thm("tlsf_free_pop_bins_pair"), [
              xs,
              hd,
              "(bl : \{bt})",
              active,
              other,
              "(us : \{lw})",
              "(vs : \{lw})",
            ]),
          ),
          arw([@lists.mem_append(), @lists.mem()]),
          @tactics.disch_tac,
          rw([
            thm(
              "tlsf_free_" +
              (if prev { "prev" } else { "next" }) +
              "_body_parts",
            ),
          ]),
          @tactics.match_mp_tac(thm("sl_seq_g")),
          @tactics.exists_tac(ap[2]),
          @tactics.thenl(
            @tactics.conj_tac,
            @list.List([
              free_lift(arg),
              seq([
                @tactics.match_mp_tac(thm("sl_seq_g")),
                @tactics.exists_tac(pp[5]),
                @tactics.thenl(
                  @tactics.conj_tac,
                  @list.List([free_lift(popth), free_lift(write)]),
                ),
              ]),
            ]),
          ),
        ]),
      )
    }
  }
}
