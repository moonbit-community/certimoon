// The strengthened take postcondition transports all old page models into
// the new physical chain before any page-initialization store executes.

///|
fn prove_tlsf_page_allocate_reserve() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let model = page_model_variables()
  let args = page_arguments(model)
  let smallmodels = page_arguments(model[8:].to_owned())
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),\{page_arguments(model[8:13].to_owned())},(lim : Num))"
  let small = "tlsf_small((d : \{w}),(hd : \{ht}),\{smallmodels})"
  let fp = "(fp : \{rty})((gs : List[Value]),(ms : Num))"
  let frame = "(gs : List[Value]) => (ms : Num) => star(\{small},\{fp})"
  let takeargs = "(d : \{w}),(word(1080) : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}),(before : \{heap}),\{frame}"
  let params = "\{args},(s : \{w}),(before : \{heap}),(fp : \{rty})"
  let vars = page_quantify(
    model +
    [
      ("s", w),
      ("before", heap),
      ("fp", rty),
      ("res", "List[Value]"),
      ("gs", "List[Value]"),
      ("ms", "Num"),
      ("h", heap),
    ],
  )
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let ws = [
    "(m : " + w + ")",
    "(top2 : " + w + ")",
    "(xs2 : " + lw + ")",
    "(hd2 : " + ht + ")",
    "(fl2 : " + w + ")",
    "(sb2 : (Num) -> " + w + ")",
    "(bl2 : " + bt + ")",
  ]
  let payload = "tlsf_bytes(val((m : \{w}))+8,val(tlsf_size((hd2 : \{ht})(m))))"
  let client = "star(\{payload},star(\{small},(fp : \{rty})((gs : List[Value]),(lim : Num))))"
  let newfacts = "tlsf_physical_ok((d : \{w}),(lim : Num),(top2 : \{w}),(xs2 : \{lw}),(hd2 : \{ht}))"
  let failure = seq([
    @tactics.disj1_tac,
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    ent_tac([thm("tlsf_allocator")], []),
  ])
  let success = seq([
    free_have(
      "!MEM((m : \{w}),(ps : \{lw}))",
      seq([
        @tactics.undisch_tac(tm(backing)),
        rw([thm("tlsf_small_backing")]),
        small_meson(ths([])),
      ]),
    ),
    free_have(
      newfacts,
      seq([
        @tactics.mp_tac(
          inst(thm("tlsf_large_facts_frame"), [
            "(d : " + w + ")",
            "(lim : Num)",
            "(top2 : " + w + ")",
            "(xs2 : " + lw + ")",
            "(hd2 : " + ht + ")",
            "(fl2 : " + w + ")",
            "(sb2 : (Num) -> " + w + ")",
            "(bl2 : " + bt + ")",
            client,
            "(h : " + heap + ")",
          ]),
        ),
        arw([]),
        small_meson(ths([])),
      ]),
    ),
    free_have(
      "(lim : Num) <= 4294967296",
      seq([
        @tactics.undisch_tac(tm(newfacts)),
        rw([thm("tlsf_physical_ok")]),
        small_meson(ths([])),
      ]),
    ),
    free_have(
      "tlsf_page_allocate_geometry((m : \{w}),val(tlsf_size((hd2 : \{ht})(m))),val((s : \{w})))",
      seq([
        @tactics.match_mp_tac(
          inst(thm("tlsf_page_allocate_large_geometry"), [
            "(d : " + w + ")",
            "(lim : Num)",
            "(top2 : " + w + ")",
            "(xs2 : " + lw + ")",
            "(hd2 : " + ht + ")",
            "(m : " + w + ")",
            "val((s : " + w + "))",
          ]),
        ),
        arw([]),
        @tactics.conv_tac(@words.word_reduce_conv),
      ]),
    ),
    @tactics.mp_tac(
      inst(
        thm("tlsf_page_allocate_allocator_frame"),
        model[0:1].to_owned().map(v => "(" + v.0 + " : " + v.1 + ")") +
        ["(xs : " + lw + ")", "(hd : " + ht + ")"] +
        model[8:13].to_owned().map(v => "(" + v.0 + " : " + v.1 + ")") +
        ["(lim : Num)", "(xs2 : " + lw + ")", "(hd2 : " + ht + ")"] +
        model[13:].to_owned().map(v => "(" + v.0 + " : " + v.1 + ")") +
        [
          "(top2 : " + w + ")",
          "(fl2 : " + w + ")",
          "(sb2 : (Num) -> " + w + ")",
          "(bl2 : " + bt + ")",
          payload,
          "(fp : " + rty + ")((gs : List[Value]),(lim : Num))",
        ],
      ),
    ),
    arw([]),
    @tactics.disch_tac,
    @tactics.disj2_tac,
    @tactics.first_x_assum(th => {
      if head_name(@kernel.concl(th)) == "star" {
        @tactics.mp_tac(th)
      } else {
        @tactics.no_tac
      }
    }),
    g => ent_tac(g.0.to_array().map(a => a.1), ws)(g),
  ])
  let _ = lemma(
    "tlsf_page_allocate_take_post",
    "\{vars} \{backing} && 8 <= val(s) && val(s) <= 256 && MOD(val(s),8) == 0 && tlsf_take_post(\{takeargs})((res : List[Value]),gs,ms,h) → tlsf_page_allocate_reserved(\{params})(res,gs,ms,h)",
    () => {
      seq([
        gen,
        rw([
          thm("tlsf_take_post"),
          thm("tlsf_allocated"),
          @words.val_word(),
          @words.dimindex_32(),
        ]),
        @tactics.conv_tac(@calc_num.num_reduce_conv),
        beta_goal(),
        strip,
        @tactics.subst1_tac(
          @kernel.assume_rule(tm("(ms : Num) == (lim : Num)")),
        ),
        rw([thm("tlsf_page_allocate_reserved")]),
        beta_goal(),
        arw([]),
        @tactics.first(@list.List([solve(failure), solve(success)])),
      ])
    },
  )
}
