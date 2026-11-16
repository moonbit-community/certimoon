// The zero table established by compiled initialization is the empty
// small-page allocator, so startup establishes the combined invariant.

///|
fn prove_tlsf_small_initialize() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let empty = "(j : Num) => (NIL : \{lw})"
  let em = "(p : \{w}) => (NIL : \{lw})"
  let zero = "(p : \{w}) => (0 : Num)"
  let z = "(word(0) : Word[8])"
  let _ = lemma(
    "tlsf_small_empty_table_item",
    "∀ d : \{w}, ∀ j : Num, tlsf_small_table_item(d,\{empty},\{empty},j) == pts(val(tlsf_base(d))+1912+8*j,REPLICATE(8,\{z}))",
    seq([
      gen,
      rw([
        thm("tlsf_small_table_item"),
        thm("tlsf_small_head"),
        thm("tlsf_small_links"),
        thm("tlsf_small_partial_links"),
        thm("star_emp_hr"),
      ]),
      @tactics.mp_tac(
        inst(thm("pts_split"), [
          "val(tlsf_base((d : \{w})))+1912+8*(j : Num)",
          "REPLICATE(4,\{z})",
          "REPLICATE(4,\{z})",
        ]),
      ),
      rw([
        @lists.length_replicate(),
        @equal.gsym(thm("tlsf_replicate_add")),
        arith("∀ a : Num, ∀ j : Num, a+1912+8*j+4 == a+1916+8*j"),
      ]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      rw([thm("tlsf_initialize_serial_zero")]),
      @meson.meson_tac(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_small_empty_table",
    "∀ d : \{w}, tlsf_small_table(d,\{empty},\{empty}) == pts(val(tlsf_base(d))+1912,REPLICATE(264,\{z}))",
    seq([
      gen,
      free_have(
        "tlsf_small_table_item((d : \{w}),\{empty},\{empty}) == ((j : Num) => pts(val(tlsf_base(d))+1912+8*j,REPLICATE(8,\{z})))",
        seq([
          rw([@class.fun_eq_thm()]),
          gen,
          rw([thm("tlsf_small_empty_table_item")]),
        ]),
      ),
      rw([thm("tlsf_small_table")]),
      arw([thm("tlsf_initialize_zero_segments")]),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
    ]),
  )
  let args = "(d : \{w}),(lim : Num),(top : \{w}),(xs : \{lw}),(hd : (\{w}) -> \{w}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : (Num) -> (Num) -> \{lw})"
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : (\{w}) -> \{w}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : (Num) -> (Num) -> \{lw}"
  let _ = lemma(
    "tlsf_allocator_empty_pages",
    "\{vars}, tlsf_allocator(\{args},NIL,\{zero},\{em},\{em},\{em},\{empty},\{empty}) == star(tlsf_large(\{args}),pts(val(tlsf_base(d))+1912,REPLICATE(264,\{z})))",
    seq([
      gen,
      rw([
        thm("tlsf_allocator"),
        thm("tlsf_small_backing"),
        thm("tlsf_small"),
        thm("tlsf_small_lists_ok"),
        thm("tlsf_small_pages_heap"),
        thm("tlsf_small_empty_table"),
        @lists.mem(),
        thm("star_emp_hl"),
        @class.eta_ax(),
      ]),
    ]),
  )
  let m = "tlsf_initialize_origin((d : \{w}))"
  let hdr = "tlsf_initialize_header((d : \{w}),(ms : Num))"
  let largeargs = "(d : \{w}),(ms : Num),\{m},[\{m}],tlsf_initialize_headers(d,ms),tlsf_push_fl(\{hdr},word(0)),tlsf_push_sb(\{hdr},(f : Num) => word(0)),tlsf_push_bl(\{hdr},\{m},(f : Num) => (j : Num) => (NIL : \{lw}))"
  let initialized = "tlsf_allocator(\{largeargs},NIL,\{zero},\{em},\{em},\{em},\{empty},\{empty})"
  let _ = lemma(
    "tlsf_initialize_establishes_allocator",
    "∀ d : \{w}, ∀ lim : Num, ∀ before : \{heap}, ∀ fp : \{rty}, ∀ res : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, tlsf_initialize_post(d,lim,before,fp,res,gs,ms,h) → res == NIL && ms == tlsf_initialize_limit(d,lim) && star(\{initialized},fp(gs,lim),h)",
    seq([
      gen,
      rw([
        thm("tlsf_initialize_post"),
        thm("tlsf_allocator_empty_pages"),
        thm("star_assoc"),
      ]),
    ]),
  )
}
