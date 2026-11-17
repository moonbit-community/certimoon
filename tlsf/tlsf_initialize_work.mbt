// Intermediate ownership while the first block is being written and published.

///|
fn define_tlsf_initialize_work() -> Unit raise {
  let w = w32
  let m = "tlsf_initialize_origin((d : \{w}))"
  let hdr = "tlsf_initialize_header((d : \{w}),(lim : Num))"
  let zero = "(f : Num) => (word(0) : \{w})"
  let empty = "(f : Num) => (j : Num) => (NIL : List[\{w}])"
  let old = "tlsf_bins((d : \{w}),word(0),\{zero},\{empty})"
  let new = "tlsf_bins((d : \{w}),tlsf_push_fl(\{hdr},word(0)),tlsf_push_sb(\{hdr},\{zero}),tlsf_push_bl(\{hdr},\{m},\{empty}))"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let table = "pts(val(tlsf_base((d : \{w})))+1912,REPLICATE(264,(word(0) : Word[8])))"
  let pending = "star(\{cell("word_add(" + m + ",word(8))","word(0)")},star(\{cell("word_add(" + m + ",word(12))","word(0)")},\{old}))"
  let bin = "if (published : Bool) { \{new} } else { \{pending} }"
  let own = "star(\{cell("tlsf_top_cell((d : " + w + "))","top")},star(\{cell(m,"h0")},star(\{cell("word_add(" + m + ",word(4))","word(0)")},star(tlsf_spare(\{m},\{hdr}),star(\{table},star(\{bin},(fp : \{rty})((gs : List[Value]),(ms : Num))))))))"
  def(
    "tlsf_initialize_work",
    "tlsf_initialize_work((d : \{w}),(lim : Num),(h0 : \{w}),(published : Bool),(top : \{w}),(fp : \{rty})) == ((gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && \{own}(h))",
  )
}

///|
fn prove_tlsf_initialize_close() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let m = "tlsf_initialize_origin(\{d})"
  let hdr = "tlsf_initialize_header(\{d},\{lim})"
  let hd = "tlsf_initialize_headers(\{d},\{lim})"
  let zero = "(f : Num) => (word(0) : \{w})"
  let empty = "(f : Num) => (j : Num) => (NIL : List[\{w}])"
  let bins = "tlsf_push_bl(\{hdr},\{m},\{empty})"
  let facts = "val(d) <= 4294965088 && lim <= 4294967296 && MOD(lim,65536) == 0 && val(tlsf_base(d))+2208 <= lim"
  let large = "tlsf_large(\{d},\{lim},\{m},[\{m}],\{hd},tlsf_push_fl(\{hdr},word(0)),tlsf_push_sb(\{hdr},\{zero}),\{bins})"
  let table = "pts(val(tlsf_base(\{d}))+1912,REPLICATE(264,(word(0) : Word[8])))"
  let _ = lemma(
    "tlsf_initialize_work_close",
    "∀ d : \{w}, ∀ lim : Num, ∀ fp : \{rty}, \{facts} → tlsf_initialize_work(d,lim,\{hdr},T,\{m},fp) == ((gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == lim && star(\{large},star(\{table},fp(gs,ms)),h))",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_initialize_header_fields"), [d, lim])),
        arw([]),
        strip,
        free_have(
          "tlsf_physical_ok(\{d},\{lim},\{m},[\{m}],\{hd})",
          seq([@tactics.match_mp_tac(thm("tlsf_initialize_physical")), arw([])]),
        ),
        free_have(
          "tlsf_bins_match([\{m}],\{hd},\{bins})",
          seq([
            rw([thm("tlsf_initialize_headers")]),
            @tactics.match_mp_tac(thm("tlsf_initialize_singleton_bins")),
            arw([]),
          ]),
        ),
        @tactics.rule_assum_tac(
          @simp.rewrite_rule(ths([thm("tlsf_initialize_headers")])),
        ),
        rw([@class.fun_eq_thm()]),
        gen,
        rw(
          [
            thm("tlsf_initialize_work"),
            thm("tlsf_large"),
            thm("tlsf_chain"),
            thm("tlsf_regions"),
            thm("tlsf_initialize_headers"),
            thm("tlsf_top_cell"),
          ] +
          lift_rws(),
        ),
        arw(
          [
            thm("star_assoc"),
            thm("star_comm"),
            thm("star_left_comm"),
            thm("star_emp_hr"),
          ] +
          lift_rws(),
        ),
      ])
    },
  )
}
