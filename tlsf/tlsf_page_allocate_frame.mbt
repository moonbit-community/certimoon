// Taking a new backing memory retains every existing small page. Its entire
// metadata and all live client payloads can therefore stay in the frame.

///|
fn prove_tlsf_page_allocate_frame() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let models = "(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls})"
  let before = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),\{models},(lim : Num))"
  let retained = "∀ p : \{w}, MEM(p,(ps : \{lw})) → MEM(p,(xs2 : \{lw})) && tlsf_used((hd2 : \{ht})(p)) && hd2(p) == (hd : \{ht})(p)"
  let vars = "∀ xs : \{lw}, ∀ hd : \{ht}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ xs2 : \{lw}, ∀ hd2 : \{ht}"
  let _ = lemma(
    "tlsf_page_allocate_retains_pages",
    "\{vars}, \{before} && tlsf_retains(xs,hd,xs2,hd2) → (\{retained})",
    seq([
      gen,
      rw([thm("tlsf_small_backing"), thm("tlsf_retains")]),
      strip,
      gen,
      @tactics.disch_tac,
      small_meson(ths([])),
    ]),
  )
  let _ = lemma(
    "tlsf_page_allocate_backing",
    "\{vars}, \{before} && tlsf_retains(xs,hd,xs2,hd2) && lim <= 4294967296 → tlsf_small_backing(xs2,hd2,\{models},lim)",
    seq([
      gen,
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_page_allocate_retains_pages"), [
          "(xs : " + lw + ")",
          "(hd : " + ht + ")",
          "(ps : " + lw + ")",
          "(sz : (" + w + ") -> Num)",
          "(loc : " + ls + ")",
          "(cached : " + ls + ")",
          "(live : " + ls + ")",
          "(lim : Num)",
          "(xs2 : " + lw + ")",
          "(hd2 : " + ht + ")",
        ]),
      ),
      arw([]),
      @tactics.disch_tac,
      @tactics.match_mp_tac(
        inst(thm("tlsf_small_backing_transport"), [
          "(xs : " + lw + ")",
          "(hd : " + ht + ")",
          "(ps : " + lw + ")",
          "(sz : (" + w + ") -> Num)",
          "(loc : " + ls + ")",
          "(cached : " + ls + ")",
          "(live : " + ls + ")",
          "(lim : Num)",
          "(xs2 : " + lw + ")",
          "(hd2 : " + ht + ")",
          "(lim : Num)",
        ]),
      ),
      arw([@arith.le_refl()]),
      gen,
      @tactics.disch_tac,
      free_have(
        "MEM((p : \{w}),(xs2 : \{lw})) && tlsf_used((hd2 : \{ht})(p)) && hd2(p) == (hd : \{ht})(p)",
        small_meson(ths([])),
      ),
      arw([]),
    ]),
  )
  let small = (hd : String) => {
    "tlsf_small((d : " +
    w +
    ")," +
    hd +
    "," +
    models +
    ",(fast : (Num) -> " +
    lw +
    "),(partial : (Num) -> " +
    lw +
    "))"
  }
  let _ = lemma(
    "tlsf_page_allocate_small_transport",
    "∀ d : \{w}, \{vars}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, \{before} && tlsf_retains(xs,hd,xs2,hd2) → \{small("hd")} == \{small("hd2")}",
    seq([
      gen,
      strip,
      @tactics.match_mp_tac(thm("tlsf_small_transport")),
      @tactics.mp_tac(
        inst(thm("tlsf_page_allocate_retains_pages"), [
          "(xs : " + lw + ")",
          "(hd : " + ht + ")",
          "(ps : " + lw + ")",
          "(sz : (" + w + ") -> Num)",
          "(loc : " + ls + ")",
          "(cached : " + ls + ")",
          "(live : " + ls + ")",
          "(lim : Num)",
          "(xs2 : " + lw + ")",
          "(hd2 : " + ht + ")",
        ]),
      ),
      arw([]),
      small_meson(ths([])),
    ]),
  )
}

///|
fn prove_tlsf_page_allocate_large_frame() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let ls = "(\{w}) -> \{lw}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let rw = (ts : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(ts))
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ top : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ p : \{w}, ∀ s : Num"
  let geom = "tlsf_page_allocate_geometry((p : \{w}),val(tlsf_size((hd : \{ht})(p))),(s : Num))"
  let _ = lemma(
    "tlsf_page_allocate_large_geometry",
    "\{vars}, tlsf_physical_ok(d,lim,top,xs,hd) && MEM(p,xs) && 1080 <= val(tlsf_size(hd(p))) && 8 <= s && s <= 256 && MOD(s,8) == 0 → \{geom}",
    seq([
      gen,
      rw([thm("tlsf_physical_ok")]),
      strip,
      @tactics.mp_tac(
        inst(thm("tlsf_layout_members"), [
          "(xs : " + lw + ")",
          "(word(0) : " + w + ")",
          "tlsf_origin((d : " + w + "))",
          "(lim : Num)",
          "(top : " + w + ")",
          "(hd : " + ht + ")",
          "(p : " + w + ")",
        ]),
      ),
      arw([]),
      rw([thm("tlsf_block_ok"), thm("tlsf_page_allocate_geometry")]),
      strip,
      arw([]),
      @int.asm_arith_tac,
    ]),
  )
  let models = "(ps : \{lw}),(sz : (\{w}) -> Num),(loc : \{ls}),(cached : \{ls}),(live : \{ls})"
  let small = (hd : String) => {
    "tlsf_small((d : " +
    w +
    ")," +
    hd +
    "," +
    models +
    ",(fast : (Num) -> " +
    lw +
    "),(partial : (Num) -> " +
    lw +
    "))"
  }
  let newlargeargs = "(d : \{w}),(lim : Num),(top2 : \{w}),(xs2 : \{lw}),(hd2 : \{ht}),(fl2 : \{w}),(sb2 : (Num) -> \{w}),(bl2 : \{bt})"
  let backing = "tlsf_small_backing((xs : \{lw}),(hd : \{ht}),\{models},(lim : Num))"
  let retained = "tlsf_retains((xs : \{lw}),(hd : \{ht}),(xs2 : \{lw}),(hd2 : \{ht}))"
  let vs = "∀ d : \{w}, ∀ xs : \{lw}, ∀ hd : \{ht}, ∀ ps : \{lw}, ∀ sz : (\{w}) -> Num, ∀ loc : \{ls}, ∀ cached : \{ls}, ∀ live : \{ls}, ∀ lim : Num, ∀ xs2 : \{lw}, ∀ hd2 : \{ht}, ∀ fast : (Num) -> \{lw}, ∀ partial : (Num) -> \{lw}, ∀ top2 : \{w}, ∀ fl2 : \{w}, ∀ sb2 : (Num) -> \{w}, ∀ bl2 : \{bt}, ∀ payload : \{hprop}, ∀ client : \{hprop}"
  let oldargs = [
    "(xs : " + lw + ")",
    "(hd : " + ht + ")",
    "(ps : " + lw + ")",
    "(sz : (" + w + ") -> Num)",
    "(loc : " + ls + ")",
    "(cached : " + ls + ")",
    "(live : " + ls + ")",
    "(lim : Num)",
    "(xs2 : " + lw + ")",
    "(hd2 : " + ht + ")",
  ]
  let _ = lemma(
    "tlsf_page_allocate_allocator_frame",
    "\{vs}, \{backing} && \{retained} && lim <= 4294967296 → star(tlsf_large(\{newlargeargs}),star(payload,star(\{small("hd")},client))) == star(tlsf_allocator(\{newlargeargs},\{models},fast,partial),star(payload,client))",
    seq([
      gen,
      strip,
      free_have(
        "tlsf_small_backing((xs2 : \{lw}),(hd2 : \{ht}),\{models},(lim : Num))",
        seq([
          @tactics.match_mp_tac(
            inst(thm("tlsf_page_allocate_backing"), oldargs),
          ),
          arw([]),
        ]),
      ),
      free_have(
        "\{small("hd")} == \{small("hd2")}",
        seq([
          @tactics.match_mp_tac(
            inst(
              thm("tlsf_page_allocate_small_transport"),
              ["(d : " + w + ")"] +
              oldargs +
              [
                "(fast : (Num) -> " + lw + ")",
                "(partial : (Num) -> " + lw + ")",
              ],
            ),
          ),
          arw([]),
        ]),
      ),
      rw([thm("tlsf_allocator")] + lift_rws()),
      arw(
        [thm("star_assoc"), thm("star_comm"), thm("star_left_comm")] +
        lift_rws(),
      ),
    ]),
  )
}
