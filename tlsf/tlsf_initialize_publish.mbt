// Publish the first free block using the already verified compiled push call.

///|
fn prove_tlsf_initialize_publish() -> Unit raise {
  let w = w32
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let arw = (xs : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(xs))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let d = "(d : \{w})"
  let lim = "(lim : Num)"
  let m = "tlsf_initialize_origin(\{d})"
  let hdr = "tlsf_initialize_header(\{d},\{lim})"
  let lc = "[\{i(m)},(l1 : Value),(l2 : Value)]"
  let oldlc = "[\{i("tlsf_base("+d+")")},(l1 : Value),(l2 : Value)]"
  let work = (h : String, published : Bool, t : String) => {
    "tlsf_initialize_work(\{d},\{lim},(\{h} : \{w}),\{if published { "T" } else { "F" }},(\{t} : \{w}),(fp : \{rty}))"
  }
  let vars = "∀ fs : List[Cl], ∀ tabs : List[(Tab_t,List[V_ref])], ∀ inst : Inst, ∀ d : \{w}, ∀ push : Num, ∀ lim : Num, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}"
  let facts = "val(d) <= 4294965088 && lim <= 4294967296 && MOD(lim,65536) == 0 && val(tlsf_base(d))+2208 <= lim"
  let native = "EL(sfunc_ind((inst : Inst),(push : Num)),(fs : List[Cl])) == Func_native(inst,Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code((d : \{w})))"
  let env = "(fs : List[Cl]),(tabs : List[(Tab_t,List[V_ref])]),(inst : Inst)"
  let zero = "(f : Num) => (word(0) : \{w})"
  let empty = "(f : Num) => (j : Num) => (NIL : List[\{w}])"
  let cell = (a : String, v : String) => {
    "pts(val((\{a} : \{w})),serialise_i32((\{v} : \{w})))"
  }
  let table = "pts(val(tlsf_base(\{d}))+1912,REPLICATE(264,(word(0) : Word[8])))"
  let own = "star(\{cell("tlsf_top_cell("+d+")","word(0)")},star(\{cell("word_add("+m+",word(4))","word(0)")},star(tlsf_spare(\{m},\{hdr}),star(\{table},(fp : \{rty})((gs : List[Value]),(ms : Num))))))"
  let frame = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == \{lim} && \{own}(h)"
  let get = sym_prove(
    "tlsf_initialize_publish_get",
    "∀ d : \{w}, ∀ lim : Num, ∀ l1 : Value, ∀ l2 : Value, ∀ fp : \{rty}, sl_triple(st(NIL,\{lc},\{work(hdr,false,"word(0)")}),[Local_get(0)],st([\{i(m)}],\{lc},\{work(hdr,false,"word(0)")}))",
    [],
    () => [],
  )
  let push = inst(thm("tlsf_ensure_push_invoke"), [
    "(fs : List[Cl])",
    "(tabs : List[(Tab_t,List[V_ref])])",
    "(inst : Inst)",
    d,
    "(push : Num)",
    m,
    lc,
    hdr,
    "(word(0) : \{w})",
    zero,
    empty,
    "(word(0) : \{w})",
    "(word(0) : \{w})",
    frame,
  ])
  let ent = ent_tac([thm("tlsf_initialize_work")], [])
  let _ = lemma(
    "tlsf_initialize_publish_parts",
    "∀ d : \{w}, ∀ push : Num, tlsf_initialize_publish(d,push) == APPEND([Local_get(0)],[Call(push),Drop])",
    () => rw([thm("tlsf_initialize_publish"), @lists.append()]),
  )
  let _ = lemma(
    "tlsf_initialize_publish_work",
    "\{vars}, \{facts} && \{native} → sl_triple_m(\{env},st(NIL,\{lc},\{work(hdr,false,"word(0)")}),tlsf_initialize_publish(d,push),st(NIL,\{lc},\{work(hdr,true,"word(0)")}),NIL)",
    () => {
      seq([
        gen,
        strip,
        @tactics.mp_tac(inst(thm("tlsf_initialize_header_fields"), [d, lim])),
        arw([]),
        strip,
        rw([thm("tlsf_initialize_publish_parts")]),
        @tactics.match_mp_tac(thm("sl_seq_m")),
        @tactics.exists_tac(
          tm("st([\{i(m)}],\{lc},\{work(hdr,false,"word(0)")})"),
        ),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            initialize_m_conseq(
              inst(get, [
                d,
                lim,
                "(l1 : Value)",
                "(l2 : Value)",
                "(fp : \{rty})",
              ]),
              ent,
              ent,
            ),
            initialize_m_conseq(push, ent, ent),
          ]),
        ),
      ])
    },
  )
  let _ = lemma(
    "tlsf_initialize_tail_work",
    "\{vars}, \{facts} && \{native} → sl_triple_m(\{env},st(NIL,\{oldlc},\{work("word(0)",false,"word(0)")}),tlsf_initialize_tail(d,push),st(NIL,\{lc},\{work(hdr,true,m)}),NIL)",
    () => {
      seq([
        gen,
        strip,
        rw([thm("tlsf_initialize_tail_parts")]),
        @tactics.match_mp_tac(thm("sl_seq_m")),
        @tactics.exists_tac(
          tm("st(NIL,\{lc},\{work("word(2)",false,"word(0)")})"),
        ),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            free_apply(thm("tlsf_initialize_mark_work")),
            seq([
              @tactics.match_mp_tac(thm("sl_seq_m")),
              @tactics.exists_tac(
                tm("st(NIL,\{lc},\{work(hdr,false,"word(0)")})"),
              ),
              @tactics.thenl(
                @tactics.conj_tac,
                @list.List([
                  free_apply(thm("tlsf_initialize_size_work")),
                  seq([
                    @tactics.match_mp_tac(thm("sl_seq_m")),
                    @tactics.exists_tac(
                      tm("st(NIL,\{lc},\{work(hdr,true,"word(0)")})"),
                    ),
                    @tactics.thenl(
                      @tactics.conj_tac,
                      @list.List([
                        free_apply(thm("tlsf_initialize_publish_work")),
                        free_apply(thm("tlsf_initialize_top_work")),
                      ]),
                    ),
                  ]),
                ]),
              ),
            ]),
          ]),
        ),
      ])
    },
  )
}
