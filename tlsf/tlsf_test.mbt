///|
test "TLSF proofs have no hypotheses and preserve the core listing" {
  @logic.load()
  let core = @logic.listing_json()
  @tlsf.load()
  @testkit.check_axioms()
  assert_eq(@logic.listing_json(), core)
  for name in @tlsf.names() {
    assert_true(@kernel.hyp(@tlsf.thm(name)).is_empty(), msg=name)
  }
}

///|
/// Execute the actual compiled search block, checking its returned word
/// and equality of the entire store. Small, deliberately sparse memories
/// expose any extra read: only the cells needed by that path are present.
test "compiled TLSF find returns candidates without changing the store" {
  @tlsf.load()
  let conv = @wasm.compute_conv([@tlsf.thm("tlsf_find_code")])
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let inst = "Inst(NIL, NIL, NIL, [0], NIL, NIL, NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let store_template = @logic.tm(
    "Wstore(NIL, NIL, [(Limit_t(0, NONE), (memory_bytes : List[Word[8]]))], NIL, NIL, NIL)",
  )
  let code = value("MAP(Basic, tlsf_find_code(word(0)))")
  // Request, first bitmap, rows (level, bitmap, slot, head), result.
  // Include both early branches, later-level masking, all null exits,
  // and alignment of an odd request. The maximum class is checked below
  // through the verified model, avoiding a deep 1908-byte literal in V8.
  for
    (request, fl, rows, expected) in [
      (16U, 1U, [(0, 1U, 0, 4096U)], 4096U),
      (17U, 2U, [(1, 1U, 0, 4096U)], 4096U),
      (48U, 4U, [(2, 256U, 8, 8192U)], 8192U),
      (48U, 4U, [(2, 1U, 0, 8192U)], 8192U),
      (16U, 0U, [], 0U),
      (16U, 1U, [(0, 0U, 0, 0U)], 0U),
      (48U, 4U, [(2, 0U, 0, 0U)], 0U),
    ] {
    let n = rows.fold(init=4, (n, row) => {
      let (f, _, j, _) = row
      Int32::max(n, 12 + 68 * f + 4 * j)
    })
    let bytes = Array::make(n, 0U)
    let put = (addr : Int32, word : UInt32) => {
      for k in 0..<4 {
        bytes[addr + k] = (word >> (8 * k)) & 255U
      }
    }
    put(0, fl)
    for (f, sb, j, head) in rows {
      put(4 + 68 * f, sb)
      put(8 + 68 * f + 4 * j, head)
    }
    let mem = @lists.mk_list(
      @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
      @kernel.type_of(byte_terms[0]),
    )
    let store = @kernel.vsubst(@list.List([(mem, memory_var)]), store_template)
    let frame = value(
      "Wframe([V_num(ConstInt32(word(\{request}))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0)))], \{inst})",
    )
    let cfg = @pair.mk_pair((store, @pair.mk_pair((frame, code))))
    let run = @wasm.run(cfg)
    assert_true(@kernel.hyp(run).is_empty())
    let (final_store, rest) = @pair.dest_pair(@kernel.rand(@kernel.concl(run)))
    let (_, es) = @pair.dest_pair(rest)
    assert_true(@basics.aconv(final_store, store), msg="store changed")
    assert_true(
      @basics.aconv(
        es,
        @logic.tm("[Basic(EConstNum(ConstInt32(word(\{expected}))))]"),
      ),
      msg="find(\{request}) returned \{@logic.show(es)}",
    )
  }
  let w = @logic.w32
  let search_defs = [
    "tlsf_search", "tlsf_search_f", "tlsf_search_j", "tlsf_align", "tlsf_round",
    "tlsf_mask", "tlsf_fli", "tlsf_cut", "tlsf_hd",
  ].map(@logic.thm)
  let model_conv = @wasm.compute_conv(search_defs)
  let maximum = computed(
    model_conv,
    @logic.tm(
      "tlsf_search((word(4160749568) : \{w}), word(134217728), (f : Num) => (if f == 27 { word(32768) } else { (word(0) : \{w}) }), (f : Num) => (j : Num) => (if f == 27 && j == 15 { [(word(12288) : \{w})] } else { (NIL : List[\{w}]) })) == word(12288)",
    ),
  )
  assert_true(@kernel.hyp(maximum).is_empty())
}

///|
/// The logic's theory as a document: __snapshot__/theory.md. It is in this
/// file so that a test run loads the logic once (each test file is its own
/// process).
test "the theory listing" (t : @test.Test) {
  t.write(@tlsf.listing())
  t.snapshot(filename="theory.md")
}

///|
/// The same as data, for the review site (tools/review_site.py):
/// __snapshot__/theory.json.
test "the theory as data" (t : @test.Test) {
  t.write(@tlsf.listing_json())
  t.snapshot(filename="theory.json")
}

///|
/// What each theorem depends on: __snapshot__/dependencies.md.
test "what each theorem depends on" (t : @test.Test) {
  t.write(@tlsf.dependencies())
  t.snapshot(filename="dependencies.md")
}

///|
/// Find the table in a triple's postcondition without unfolding the code
/// or the heap assertions.
fn tlsf_bins_args(t : @kernel.Term) -> Array[@kernel.Term]? {
  if @logic.args_of(t, "tlsf_bins", 4) is Some(args) {
    return Some(args)
  }
  match t {
    Comb(f, x) =>
      match tlsf_bins_args(f) {
        Some(args) => Some(args)
        None => tlsf_bins_args(x)
      }
    Abs(_, body) => tlsf_bins_args(body)
    _ => None
  }
}

///|
/// Instantiate the verified triples and compute their table updates.
/// Cover the list positions, both bitmap-clearing cases, and upper indices.
test "all-bins push and pop update bins and bitmap levels" {
  @tlsf.load()
  let conv = @wasm.compute_conv([@tlsf.thm("tlsf_upd")])
  let w = @logic.w32
  let lw = "List[\{w}]"
  let nil = "(NIL : \{lw})"
  let m = "(word(4096) : \{w})"
  let a = "(word(8192) : \{w})"
  let b = "(word(12288) : \{w})"
  let extra = "(word(16384) : \{w})"
  // size, level, bin, prefix, suffix, another level/bin (or -1),
  // old fl/sb, expected fl/sb after pop
  for
    (size, f, j, ys, zs, of, oj, fl, sb, fl_after, sb_after) in [
      ("16", 0, 0, nil, nil, -1, -1, "1", "1", "0", "0"),
      ("16", 0, 0, nil, nil, 0, 1, "1", "3", "1", "2"),
      ("16", 0, 0, nil, nil, 1, 0, "3", "1", "2", "0"),
      ("16", 0, 0, nil, "[\{a}]", -1, -1, "1", "1", "1", "1"),
      ("16", 0, 0, "[\{a}]", nil, -1, -1, "1", "1", "1", "1"),
      ("16", 0, 0, "[\{a}]", "[\{b}]", -1, -1, "1", "1", "1", "1"),
      ("4160749568", 27, 15, nil, nil, -1, -1, "134217728", "32768", "0", "0"),
    ] {
    let before = "APPEND(\{ys}, CONS(\{m}, \{zs}))"
    let after = "APPEND(\{ys}, \{zs})"
    let sb_other = if of < 0 {
      "word(0)"
    } else {
      "if f == \{of} { word(1) } else { word(0) }"
    }
    let sbt = "(f : Num) => if f == \{f} { (word(\{sb}) : \{w}) } else { \{sb_other} }"
    let other = if of < 0 {
      nil
    } else {
      "if f == \{of} && j == \{oj} { [\{extra}] } else { \{nil} }"
    }
    let bl = "(f : Num) => (j : Num) => if f == \{f} && j == \{j} { \{before} } else { \{other} }"
    let vals : Map[String, @kernel.Term] = {
      "d": @logic.tm("(word(0) : \{w})"),
      "m": @logic.tm(m),
      "hd": @logic.tm("(word(\{size}) : \{w})"),
      "fl": @logic.tm("(word(\{fl}) : \{w})"),
      "sb": @logic.tm(sbt),
      "bl": @logic.tm(bl),
      "ys": @logic.tm(ys),
      "zs": @logic.tm(zs),
    }
    let pop = instantiate(@tlsf.thm("tlsf_pop_all"), vals)
    let (pre, _) = @basics.dest_imp(@kernel.concl(pop))
    let pop = @bool.mp(pop, computed(conv, pre))
    assert_true(@kernel.hyp(pop).is_empty())
    guard @logic.args_of(@kernel.concl(pop), "sl_triple", 3)
      is Some([_, _, post]) else {
      fail("pop is not a triple")
    }
    guard tlsf_bins_args(post) is Some([_, new_fl, new_sb, new_bl]) else {
      fail("pop has no table postcondition")
    }
    for
      fact in [
        "(\{@logic.show(new_fl)}) == (word(\{fl_after}) : \{w})",
        "(\{@logic.show(new_sb)})(\{f}) == (word(\{sb_after}) : \{w})",
        "(\{@logic.show(new_bl)})(\{f})(\{j}) == \{after}",
        "(\{@logic.show(new_sb)})(\{(f + 1) % 28}) == (\{sbt})(\{(f + 1) % 28})",
        "(\{@logic.show(new_bl)})(\{(f + 1) % 28})(0) == (\{bl})(\{(f + 1) % 28})(0)",
        "(\{@logic.show(new_bl)})(\{f})(\{(j + 1) % 16}) == (\{bl})(\{f})(\{(j + 1) % 16})",
      ] {
      assert_true(
        @kernel.hyp(computed(conv, @logic.tm(fact))).is_empty(),
        msg=fact,
      )
    }
    // Push back onto the remaining bin: both bitmaps return to their
    // original values, including when pop emptied the bin or the level.
    vals["fl"] = new_fl
    vals["sb"] = new_sb
    vals["bl"] = new_bl
    vals["pf0"] = @logic.tm("tlsf_prev(\{ys})")
    vals["nf0"] = @logic.tm("tlsf_hd(\{zs})")
    let push = instantiate(@tlsf.thm("tlsf_push_all"), vals)
    let (pre, _) = @basics.dest_imp(@kernel.concl(push))
    let push = @bool.mp(push, computed(conv, pre))
    assert_true(@kernel.hyp(push).is_empty())
    guard @logic.args_of(@kernel.concl(push), "sl_triple", 3)
      is Some([_, _, post]) else {
      fail("push is not a triple")
    }
    guard tlsf_bins_args(post) is Some([_, new_fl, new_sb, new_bl]) else {
      fail("push has no table postcondition")
    }
    for
      fact in [
        "(\{@logic.show(new_fl)}) == (word(\{fl}) : \{w})",
        "(\{@logic.show(new_sb)})(\{f}) == (word(\{sb}) : \{w})",
        "(\{@logic.show(new_bl)})(\{f})(\{j}) == CONS(\{m}, \{after})",
        "(\{@logic.show(new_bl)})(\{f})(\{(j + 1) % 16}) == (\{bl})(\{f})(\{(j + 1) % 16})",
      ] {
      assert_true(
        @kernel.hyp(computed(conv, @logic.tm(fact))).is_empty(),
        msg=fact,
      )
    }
  }
}

///|
test "physical TLSF layout and exact bin correspondence" {
  @tlsf.load()
  let inst = (th : @kernel.Thm, args : Array[String]) => {
    @bool.ispecl(@list.List(args.map(@logic.tm)), th)
  }
  let w = @logic.w32
  let lw = "List[\{w}]"
  let zero = "(word(0) : \{w})"
  let names = [
    "tlsf_size", "tlsf_used", "tlsf_last", "tlsf_level_of", "tlsf_slot_of", "tlsf_block_ok",
    "tlsf_layout", "tlsf_base", "tlsf_origin", "tlsf_count", "tlsf_coalesced", "tlsf_physical_ok",
    "tlsf_spare",
  ]
  let conv = @wasm.compute_conv(
    names.map(@logic.thm) + [@lists.mem(), @lists.filter(), @lists.length()],
  )
  let fact = (s : String) => {
    let reduced = conv(@logic.tm(s))
    let proof = @bool.eqt_elim(reduced) catch {
      _ =>
        raise Failure(
          "fixture: " +
          s +
          "\ncomputed: " +
          @logic.show(@equal.rhs(@kernel.concl(reduced))),
        )
    }
    assert_true(@kernel.hyp(proof).is_empty(), msg=s)
  }
  let hd = "(m : \{w}) => if m == word(2176) { word(1024) } else { if m == word(3208) { word(513) } else { word(61802) } }"
  let xs = "[(word(2176) : \{w}), word(3208), word(3728)]"
  fact("tlsf_physical_ok(\{zero}, 65536, word(3728), \{xs}, \{hd})")
  fact("tlsf_spare((word(3208) : \{w}), word(513)) == emp")
  fact("tlsf_spare((word(2176) : \{w}), word(1024)) == tlsf_bytes(2192, 1016)")
  fact(
    "!tlsf_block_ok(2176, 65536, (word(2176) : \{w}), (m : \{w}) => word(1028))",
  )
  fact("!tlsf_physical_ok(\{zero}, 65536, \{zero}, (NIL : \{lw}), \{hd})")
  for
    bad in [
      // A gap in the physical chain.
      "tlsf_physical_ok(\{zero}, 65536, word(3728), [(word(2176) : \{w}), word(3216), word(3728)], \{hd})",
      // A last flag on an interior block.
      "tlsf_physical_ok(\{zero}, 65536, word(3728), \{xs}, (m : \{w}) => if m == word(2176) { word(1026) } else { (\{hd})(m) })",
      // The stored top must be the final physical block.
      "tlsf_physical_ok(\{zero}, 65536, word(3208), \{xs}, \{hd})",
      // Two neighbouring blocks cannot both be free in a stable state.
      "tlsf_physical_ok(\{zero}, 65536, word(3728), \{xs}, (m : \{w}) => if m == word(3208) { word(512) } else { (\{hd})(m) })",
    ] {
    fact("!(\{bad})")
  }
  for
    (lim, size, f, j) in [
      ("65536", "63352", 11, 14),
      ("4294967296", "4294965112", 27, 15),
    ] {
    let m = "(word(2176) : \{w})"
    let hs = "(m : \{w}) => (word_add(word(\{size}), word(2)) : \{w})"
    let single = "[\{m}]"
    let bl = "(f : Num) => (j : Num) => if f == \{f} && j == \{j} { \{single} } else { (NIL : \{lw}) }"
    fact("tlsf_physical_ok(\{zero}, \{lim}, \{m}, \{single}, \{hs})")
    fact(
      "tlsf_level_of((\{hs})(\{m})) == \{f} && tlsf_slot_of((\{hs})(\{m})) == \{j}",
    )
    if lim == "4294967296" {
      fact("!tlsf_physical_ok(\{zero}, 0, \{m}, \{single}, \{hs})")
    }
    let gen = @tactics.repeat_tac(@tactics.gen_tac)
    let arw = (rws : Array[@kernel.Thm]) => {
      @simp.asm_rewrite_tac(@logic.ths(rws))
    }
    let matching = @tactics.prove(
      @logic.tm("tlsf_bins_match(\{single}, \{hs}, \{bl})"),
      @logic.seq([
        @simp.rewrite_tac(@logic.ths([@tlsf.thm("tlsf_bins_match")])),
        @tactics.thenl(
          @tactics.conj_tac,
          @list.List([
            @logic.seq([
              gen,
              @tactics.conv_tac(conv),
              @tactics.repeat_tac(@tactics.strip_tac),
              @logic.subst_vars(),
              arw([]),
              @tactics.conv_tac(conv),
            ]),
            @logic.seq([
              gen,
              @class.asm_cases_tac(
                @logic.tm("(f : Num) == \{f} && (j : Num) == \{j}"),
              ),
              arw([@lists.mem()]),
              @tactics.conv_tac(conv),
              @meson.asm_meson_tac(@logic.ths([])),
            ]),
          ]),
        ),
      ]),
    )
    assert_true(@kernel.hyp(matching).is_empty())
    for
      (bad_bl, cf, cj) in [
        // A repeated address in the right bin.
        (
          "(f : Num) => (j : Num) => if f == \{f} && j == \{j} { [\{m}, \{m}] } else { (NIL : \{lw}) }",
          f,
          j,
        ),
        // A missing free block.
        ("(f : Num) => (j : Num) => (NIL : \{lw})", f, j),
        // A free block in the wrong class.
        (
          "(f : Num) => (j : Num) => if f == \{f} && j == \{(j + 1) % 16} { \{single} } else { (NIL : \{lw}) }",
          f,
          (j + 1) % 16,
        ),
      ] {
      let exact = inst(@tlsf.thm("tlsf_bins_match_exact"), [
        single,
        hs,
        bad_bl,
        m,
        cf.to_string(),
        cj.to_string(),
      ])
      let rejected = @tactics.prove(
        @logic.tm("!tlsf_bins_match(\{single}, \{hs}, \{bad_bl})"),
        @logic.seq([@tactics.mp_tac(exact), @tactics.conv_tac(conv)]),
      )
      assert_true(@kernel.hyp(rejected).is_empty())
    }
    let used_hd = "(m : \{w}) => (word_add(word(\{size}), word(3)) : \{w})"
    let used_exact = inst(@tlsf.thm("tlsf_bins_match_exact"), [
      single,
      used_hd,
      bl,
      m,
      f.to_string(),
      j.to_string(),
    ])
    let rejected = @tactics.prove(
      @logic.tm("!tlsf_bins_match(\{single}, \{used_hd}, \{bl})"),
      @logic.seq([@tactics.mp_tac(used_exact), @tactics.conv_tac(conv)]),
    )
    assert_true(@kernel.hyp(rejected).is_empty())
  }
}

///|
test "compiled TLSF split keeps the whole block at the strict threshold" {
  @tlsf.load()
  let conv = @wasm.compute_conv([@tlsf.thm("tlsf_split_code")])
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let inst = "Inst(NIL, NIL, NIL, [0], NIL, NIL, NIL)"
  let code = value("MAP(Basic, tlsf_split_code(word(0), 0))")
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = @logic.tm(
    "Wstore(NIL, NIL, [(Limit_t(0, NONE), (memory_bytes : List[Word[8]]))], NIL, NIL, NIL)",
  )
  for
    (request, size, last) in [(16U, 280U, 0U), (16U, 280U, 2U), (16U, 272U, 2U)] {
    let before = Array::makei(64, n => (n * 19 + 7).to_uint() & 255U)
    for k in 0..<4 {
      before[32 + k] = ((size | last) >> (8 * k)) & 255U
    }
    let after = before.copy()
    after[32] = after[32] | 1U
    let store = (bytes : Array[UInt32]) => {
      let mem = @lists.mk_list(
        @list.List(bytes.map(x => byte_terms[(x & 255U).reinterpret_as_int()])),
        @kernel.type_of(byte_terms[0]),
      )
      @kernel.vsubst(@list.List([(mem, memory_var)]), template)
    }
    let frame = value(
      "Wframe([V_num(ConstInt32(word(32))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(\{request}))), V_num(ConstInt32(word(0))), V_num(ConstInt32(word(0)))], \{inst})",
    )
    let run = @wasm.run(
      @pair.mk_pair((store(before), @pair.mk_pair((frame, code)))),
    )
    assert_true(@kernel.hyp(run).is_empty())
    let (final_store, rest) = @pair.dest_pair(@kernel.rand(@kernel.concl(run)))
    assert_true(
      @basics.aconv(final_store, store(after)),
      msg="split changed bytes outside the used flag",
    )
    assert_true(
      @basics.aconv(@pair.dest_pair(rest).1, @logic.tm("(NIL : List[Einstr])")),
    )
  }
}

///|
test "TLSF split models preserve physical geometry and remainder flags" {
  @tlsf.load()
  let w = @logic.w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let names = [
    "tlsf_size", "tlsf_used", "tlsf_last", "tlsf_block_ok", "tlsf_layout", "tlsf_coalesced",
    "tlsf_physical_ok", "tlsf_base", "tlsf_origin", "tlsf_mark", "tlsf_put", "tlsf_remainder",
    "tlsf_remainder_size", "tlsf_split_headers",
  ]
  let conv = @wasm.compute_conv(names.map(@logic.thm))
  let fact = (s : String) => {
    let th = computed(conv, @logic.tm(s))
    assert_true(@kernel.hyp(th).is_empty(), msg=s)
  }
  let m = "(word(2176) : \{w})"
  let hd = "(x : \{w}) => (word(63354) : \{w})"
  let nh = "tlsf_split_headers(\{hd}, \{m}, (word(16) : \{w}))"
  fact("tlsf_physical_ok((word(0) : \{w}), 65536, \{m}, [\{m}], \{hd})")
  fact(
    "tlsf_physical_ok((word(0) : \{w}), 65536, word(2200), [\{m}, word(2200)], \{nh})",
  )
  fact(
    "(\{nh})(\{m}) == word(17) && (\{nh})((word(2200) : \{w})) == word(63330)",
  )
  // An interior split retains the old top and makes its successor used.
  let ih = "(x : \{w}) => if x == word(2176) { word(288) } else { (word(63059) : \{w}) }"
  let split = "tlsf_split_headers(\{ih}, \{m}, (word(16) : \{w}))"
  fact(
    "tlsf_physical_ok((word(0) : \{w}), 65536, word(2472), [\{m}, word(2472)], \{ih})",
  )
  fact(
    "tlsf_physical_ok((word(0) : \{w}), 65536, word(2472), [\{m}, word(2200), word(2472)], \{split})",
  )
  fact("(\{split})((word(2200) : \{w})) == word(264)")
  // The physical endpoint may be 2^32, without wrapping the last header.
  let maxh = "(x : \{w}) => (word(4294965114) : \{w})"
  let maxsplit = "tlsf_split_headers(\{maxh}, \{m}, (word(4160749568) : \{w}))"
  fact(
    "tlsf_physical_ok((word(0) : \{w}), 4294967296, word(4160751752), [\{m}, word(4160751752)], \{maxsplit})",
  )
  for low in 0..<4 {
    fact(
      "tlsf_size(word_and(word_or((word(264) : \{w}), word(\{low})), word(4294967294))) == word(264)",
    )
  }
  ignore((lw, ht))
}

///|
/// Execute the complete native closure, including its real helper calls
/// and early return. Compare every byte, including payload canaries.
test "compiled TLSF take calls pop and preserves all other bytes" {
  @tlsf.load()
  let conv = @wasm.compute_conv([
    @tlsf.thm("tlsf_take_code"),
    @tlsf.thm("tlsf_pop_code"),
    @tlsf.thm("tlsf_push_code"),
  ])
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let instance = "Inst(NIL, [0, 1, 2], NIL, [0], NIL, NIL, NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = value(
    "Wstore([Func_native(\{instance}, Tf([T_num(T_i32)], NIL), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_pop_code(word(0))), Func_native(\{instance}, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_push_code(word(0))), Func_native(\{instance}, Tf([T_num(T_i32)], [T_num(T_i32)]), [T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32), T_num(T_i32)], tlsf_take_code(word(0), 0, 1))], NIL, [(Limit_t(0, NONE), (memory_bytes : List[Word[8]]))], NIL, NIL, NIL)",
  )
  let store = (bytes : Array[UInt32]) => {
    let mem = @lists.mk_list(
      @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
      @kernel.type_of(byte_terms[0]),
    )
    @kernel.vsubst(@list.List([(mem, memory_var)]), template)
  }
  let frame = value("Wframe([V_num(ConstInt32(word(123)))], \{instance})")
  for
    (request, populated, successor) in [
      (16U, false, false),
      (16U, true, false),
      (16U, true, true),
      (17U, true, false),
    ] {
    let level = if request == 17U { 1 } else { 0 }
    let size = if request == 17U { 32U } else { 16U }
    let before = Array::makei(
      if level == 1 {
        112
      } else if successor {
        112
      } else {
        64
      },
      n => (n * 19 + 7).reinterpret_as_uint() & 255U,
    )
    let put = (bytes : Array[UInt32], addr : Int32, word : UInt32) => {
      for k in 0..<4 {
        bytes[addr + k] = (word >> (8 * k)) & 255U
      }
    }
    put(before, 0, if populated { 1U << level } else { 0U })
    put(before, 4 + 68 * level, if populated { 1U } else { 0U })
    put(before, 8 + 68 * level, if populated { 32U } else { 0U })
    put(before, 32, size | (if successor { 0U } else { 2U }))
    put(before, 40, 0U)
    put(before, 44, if successor { 80U } else { 0U })
    if successor {
      put(before, 56, 17U)
      put(before, 80, 18U)
      put(before, 88, 32U)
      put(before, 92, 0U)
    }
    let after = before.copy()
    if populated {
      put(after, 32, size | (if successor { 1U } else { 3U }))
      put(after, 8 + 68 * level, if successor { 80U } else { 0U })
      if successor {
        put(after, 88, 0U)
      } else {
        put(after, 0, 0U)
        put(after, 4 + 68 * level, 0U)
      }
    }
    let code = value(
      "[Basic(EConstNum(ConstInt32(word(\{request})))), Basic(Call(2))]",
    )
    let run = @wasm.run(
      @pair.mk_pair((store(before), @pair.mk_pair((frame, code)))),
    )
    assert_true(@kernel.hyp(run).is_empty())
    let (final_store, rest) = @pair.dest_pair(@kernel.rand(@kernel.concl(run)))
    let (final_frame, es) = @pair.dest_pair(rest)
    assert_true(
      @basics.aconv(final_store, store(after)),
      msg="take changed unexpected bytes",
    )
    assert_true(
      @basics.aconv(final_frame, frame),
      msg="take changed the caller frame",
    )
    let expected = if populated { 32 } else { 0 }
    assert_true(
      @basics.aconv(
        es,
        @logic.tm("[Basic(EConstNum(ConstInt32(word(\{expected}))))]"),
      ),
      msg="wrong take result",
    )
  }
  // A non-last split also exercises the real push closure. Metadata is
  // deliberately sparse; the theorem covers the full physical invariant.
  let before = Array::makei(352, n => (n * 19 + 7).reinterpret_as_uint() & 255U)
  let put = (bytes : Array[UInt32], addr : Int32, word : UInt32) => {
    for k in 0..<4 {
      bytes[addr + k] = (word >> (8 * k)) & 255U
    }
  }
  for
    (addr, word) in [
      (0, 16U),
      (32, 288U),
      (40, 0U),
      (44, 0U),
      (276, 4U),
      (280, 0U),
      (288, 32U),
      (328, 19U),
      (332, 32U),
    ] {
    put(before, addr, word)
  }
  let after = before.copy()
  for
    (addr, word) in [
      (32, 17U),
      (56, 264U),
      (60, 32U),
      (64, 0U),
      (68, 0U),
      (276, 1U),
      (280, 56U),
      (288, 0U),
      (332, 56U),
    ] {
    put(after, addr, word)
  }
  let run = @wasm.run(
    @pair.mk_pair(
      (
        store(before),
        @pair.mk_pair(
          (
            frame,
            value("[Basic(EConstNum(ConstInt32(word(16)))), Basic(Call(2))]"),
          ),
        ),
      ),
    ),
  )
  assert_true(@kernel.hyp(run).is_empty())
  let (final_store, rest) = @pair.dest_pair(@kernel.rand(@kernel.concl(run)))
  let (final_frame, es) = @pair.dest_pair(rest)
  assert_true(
    @basics.aconv(final_store, store(after)),
    msg="take split changed unexpected bytes",
  )
  assert_true(@basics.aconv(final_frame, frame))
  assert_true(
    @basics.aconv(es, @logic.tm("[Basic(EConstNum(ConstInt32(word(32))))]")),
  )
}

///|
test "TLSF ensure page rounding and memory32 endpoint arithmetic" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_ensure_expected", "tlsf_ensure_pages", "tlsf_align", "tlsf_round", "tlsf_mask",
      "tlsf_fli", "tlsf_size", "tlsf_used", "tlsf_last", "tlsf_capacity_at", "tlsf_extend_headers",
      "tlsf_append_headers", "tlsf_put", "tlsf_level_of", "tlsf_slot_of", "tlsf_physical_ok",
      "tlsf_block_ok", "tlsf_layout", "tlsf_coalesced", "tlsf_base", "tlsf_origin",
    ].map(@logic.thm),
  )
  for
    (request, header, pages) in [
      (16U, 3U, 1U),
      (17U, 3U, 1U),
      (4160749568U, 3U, 63489U),
      (16U, 65514U, 0U),
      (17U, 18U, 1U),
      (65536U, 65514U, 1U),
      // A caller that has not exhausted reusable blocks can underflow the
      // free-top subtraction. Safety must also cover this shipped behavior.
      (16U, 131050U, 65535U),
    ] {
    let th = conv(
      @logic.tm(
        "tlsf_ensure_pages((word(\{request}) : Word[32]),word(\{header})) == word(\{pages})",
      ),
    )
    assert_true(@kernel.hyp(th).is_empty())
    assert_true(@basics.aconv(@equal.rhs(@kernel.concl(th)), @logic.tm("T")))
  }
  for
    formula in [
      "(tlsf_capacity_at(4294967296,(word(32) : Word[32])) == word(4294967256))",
      "(tlsf_capacity_at(131072,(word(65536) : Word[32])) == word(65528))", "tlsf_extend_headers((x : Word[32]) => word(63354),word(2176),131072,word(2176)) == word(128890)",
      "tlsf_append_headers((x : Word[32]) => word(63355),word(2176),65536,131072,word(2176)) == word(63353)",
      "tlsf_append_headers((x : Word[32]) => word(63355),word(2176),65536,131072,word(65536)) == word(65530)",
      "tlsf_level_of((word(63354) : Word[32])) == 11 && tlsf_slot_of(word(63354)) == 14",
      "tlsf_level_of((word(128890) : Word[32])) == 12 && tlsf_slot_of(word(128890)) == 15",
      "tlsf_used((word(63353) : Word[32])) && !tlsf_last(word(63353)) && !tlsf_used(word(65530)) && tlsf_last(word(65530))",
    ] {
    let th = conv(@logic.tm(formula))
    assert_true(@kernel.hyp(th).is_empty())
    assert_true(
      @basics.aconv(@equal.rhs(@kernel.concl(th)), @logic.tm("T")),
      msg=formula,
    )
  }
  let m = "(word(2176) : Word[32])"
  let free_headers = "(x : Word[32]) => word(63354)"
  let used_headers = "(x : Word[32]) => word(63355)"
  for
    formula in [
      "tlsf_physical_ok((word(0) : Word[32]),131072,\{m},[\{m}],tlsf_extend_headers(\{free_headers},\{m},131072))",
      "tlsf_physical_ok((word(0) : Word[32]),131072,word(65536),[\{m},word(65536)],tlsf_append_headers(\{used_headers},\{m},65536,131072))",
      // A used top can grow the memory to exactly 4 GiB. Its new address
      // fits in i32 even though memory.size << 16 becomes the word zero.
      "tlsf_physical_ok((word(0) : Word[32]),4294967296,word(4294901760),[\{m},word(4294901736),word(4294901760)],tlsf_append_headers((x : Word[32]) => if x == word(2176) { word(4294899553) } else { word(19) },word(4294901736),4294901760,4294967296))",
    ] {
    let th = conv(@logic.tm(formula))
    assert_true(@kernel.hyp(th).is_empty())
    assert_true(
      @basics.aconv(@equal.rhs(@kernel.concl(th)), @logic.tm("T")),
      msg=formula,
    )
  }
}

///|
// Sparse execution fixtures isolate all branches of the shipped function.
// The symbolic theorem additionally requires the complete allocator invariant.
test "compiled TLSF free coalesces and preserves every other byte" {
  @tlsf.load()
  let conv = @wasm.compute_conv([
    @tlsf.thm("tlsf_free_code"),
    @tlsf.thm("tlsf_pop_code"),
    @tlsf.thm("tlsf_push_code"),
  ])
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let instance = "Inst(NIL,[0,1,2],NIL,[0],NIL,NIL,NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = value(
    "Wstore([Func_native(\{instance},Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code(word(0))),Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(word(0))),Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32)],tlsf_free_code(word(0),0,1))],NIL,[(Limit_t(0,NONE),(memory_bytes : List[Word[8]]))],NIL,NIL,NIL)",
  )
  let store = (bytes : Array[UInt32]) => {
    let mem = @lists.mk_list(
      @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
      @kernel.type_of(byte_terms[0]),
    )
    @kernel.vsubst(@list.List([(mem, memory_var)]), template)
  }
  let put = (bytes : Array[UInt32], addr : Int32, word : UInt32) => {
    for k in 0..<4 {
      bytes[addr + k] = (word >> (8 * k)) & 255U
    }
  }
  let frame = value("Wframe([V_num(ConstInt32(word(123)))],\{instance})")
  let code = value("[Basic(EConstNum(ConstInt32(word(280)))),Basic(Call(2))]")
  let mut cases = 0
  for pred in 0..<3 {
    for succ in 0..<4 {
      // End coalescing is covered by the path theorems and model fixtures
      // below; keep concrete memories small, as in the search tests.
      if succ == 2 || (pred == 2 && succ == 0) {
        continue
      }
      for reverse in [false, true] {
        let before = Array::makei(448, n => {
          (n * 19 + 7).reinterpret_as_uint() & 255U
        })
        let p = 256
        let m = 280
        let r = 304
        let n = 328
        let top = if succ == 0 { m } else if succ == 3 { n } else { r }
        put(before, p, if pred == 2 { 16U } else { 17U })
        put(before, p + 4, 0U)
        put(before, m, if succ == 0 { 19U } else { 17U })
        put(before, m + 4, if pred == 0 { 0U } else { p.reinterpret_as_uint() })
        put(
          before,
          r,
          if succ == 1 {
            19U
          } else if succ == 2 {
            18U
          } else {
            16U
          },
        )
        put(before, r + 4, m.reinterpret_as_uint())
        put(before, n, 19U)
        put(before, n + 4, r.reinterpret_as_uint())
        ignore(top)
        let nodes : Array[Int32] = []
        if pred == 2 {
          nodes.push(p)
        }
        if succ >= 2 {
          nodes.push(r)
        }
        // Include empty, singleton, head, tail, and interior removals.
        let extra = (pred + succ) % 3
        if extra >= 1 {
          nodes.insert(0, 384)
        }
        if extra >= 2 {
          nodes.push(416)
        }
        if reverse {
          for k in 0..<(nodes.length() / 2) {
            let x = nodes[k]
            nodes[k] = nodes[nodes.length() - 1 - k]
            nodes[nodes.length() - 1 - k] = x
          }
        }
        for k, x in nodes {
          put(
            before,
            x + 8,
            if k == 0 {
              0U
            } else {
              nodes[k - 1].reinterpret_as_uint()
            },
          )
          put(
            before,
            x + 12,
            if k + 1 == nodes.length() {
              0U
            } else {
              nodes[k + 1].reinterpret_as_uint()
            },
          )
        }
        put(before, 0, if nodes.is_empty() { 0U } else { 1U })
        put(before, 4, if nodes.is_empty() { 0U } else { 1U })
        put(
          before,
          8,
          if nodes.is_empty() {
            0U
          } else {
            nodes[0].reinterpret_as_uint()
          },
        )
        for addr in [72, 92, 140, 144] {
          put(before, addr, 0U)
        }
        let after = before.copy()
        let pop = (x : Int32) => {
          let k = nodes.search(x).unwrap()
          let prev = if k == 0 { 0 } else { nodes[k - 1] }
          let next = if k + 1 == nodes.length() { 0 } else { nodes[k + 1] }
          if prev == 0 {
            put(after, 8, next.reinterpret_as_uint())
          } else {
            put(after, prev + 12, next.reinterpret_as_uint())
          }
          if next != 0 {
            put(after, next + 8, prev.reinterpret_as_uint())
          }
          ignore(nodes.remove(k))
          if nodes.is_empty() {
            put(after, 0, 0U)
            put(after, 4, 0U)
          }
        }
        put(after, m, if succ == 0 { 18U } else { 16U })
        let mut active = m
        let mut size = 16U
        if pred == 2 {
          pop(p)
          active = p
          size = size + 24U
          put(after, active, size | (if succ == 0 { 2U } else { 0U }))
          if succ == 0 {
            put(after, 1908, active.reinterpret_as_uint())
          } else {
            put(after, r + 4, active.reinterpret_as_uint())
          }
        }
        if succ >= 2 {
          pop(r)
          size = size + 24U
          put(after, active, size | (if succ == 2 { 2U } else { 0U }))
          if succ == 2 {
            put(after, 1908, active.reinterpret_as_uint())
          } else {
            put(after, n + 4, active.reinterpret_as_uint())
          }
        }
        let (level, slot) = if size == 16U {
          (0, 0)
        } else if size == 40U {
          (1, 4)
        } else {
          (2, 0)
        }
        let head = if level == 0 && !nodes.is_empty() { nodes[0] } else { 0 }
        put(after, active + 8, 0U)
        put(after, active + 12, head.reinterpret_as_uint())
        if head != 0 {
          put(after, head + 8, active.reinterpret_as_uint())
        }
        put(after, 8 + 68 * level + 4 * slot, active.reinterpret_as_uint())
        put(after, 4 + 68 * level, 1U << slot)
        put(after, 0, (if nodes.is_empty() { 0U } else { 1U }) | (1U << level))
        let run = @wasm.run(
          @pair.mk_pair((store(before), @pair.mk_pair((frame, code)))),
        )
        assert_true(@kernel.hyp(run).is_empty())
        let (final_store, rest) = @pair.dest_pair(
          @kernel.rand(@kernel.concl(run)),
        )
        let (final_frame, es) = @pair.dest_pair(rest)
        assert_true(
          @basics.aconv(final_store, store(after)),
          msg="free bytes: pred=\{pred} succ=\{succ} reverse=\{reverse}",
        )
        assert_true(
          @basics.aconv(final_frame, frame),
          msg="free changed caller frame",
        )
        assert_true(
          @basics.aconv(
            es,
            @logic.tm("[Basic(EConstNum(ConstInt32(word(0))))]"),
          ),
          msg="free result",
        )
        cases = cases + 1
      }
    }
  }
  assert_eq(cases, 16)
}

///|
test "TLSF coalescing models restore geometry including the memory32 endpoint" {
  @tlsf.load()
  let w = @logic.w32
  let defs = [
    "tlsf_size", "tlsf_used", "tlsf_last", "tlsf_block_ok", "tlsf_layout", "tlsf_coalesced",
    "tlsf_physical_ok", "tlsf_base", "tlsf_origin", "tlsf_mark", "tlsf_put", "tlsf_release",
    "tlsf_merge_size", "tlsf_merge_header", "tlsf_merge_headers", "tlsf_free_geom",
    "tlsf_free_covers", "tlsf_free_live", "tlsf_level_of", "tlsf_slot_of",
  ]
  let conv = @wasm.compute_conv(defs.map(@logic.thm))
  let fact = (s : String) => {
    let reduced = conv(@logic.tm(s))
    let th = @bool.eqt_elim(reduced) catch {
      _ =>
        raise Failure(
          "coalescing fixture: \{s}\ncomputed: \{@logic.show(@equal.rhs(@kernel.concl(reduced)))}",
        )
    }
    assert_true(@kernel.hyp(th).is_empty(), msg=s)
  }
  let zero = "(word(0) : \{w})"
  let p = "(word(2176) : \{w})"
  let m = "(word(2200) : \{w})"
  let r = "(word(2224) : \{w})"
  let tail = "(word(2248) : \{w})"
  let xs = "[\{p},\{m},\{r},\{tail}]"
  let hd = "(x : \{w}) => if x == \{p} { word(16) } else { if x == \{m} { word(17) } else { if x == \{r} { word(16) } else { word(63283) } } }"
  let released = "tlsf_release(\{hd},\{m})"
  let left = "tlsf_merge_headers(\{released},\{p},\{m})"
  let both = "tlsf_merge_headers(\{left},\{p},\{r})"
  fact("tlsf_physical_ok(\{zero},65536,\{tail},\{xs},\{hd})")
  fact("!tlsf_physical_ok(\{zero},65536,\{tail},\{xs},\{released})")
  fact("tlsf_free_geom(\{zero},65536,\{tail},\{xs},\{released},\{m})")
  fact("tlsf_free_geom(\{zero},65536,\{tail},[\{p},\{r},\{tail}],\{left},\{p})")
  fact("!tlsf_physical_ok(\{zero},65536,\{tail},[\{p},\{r},\{tail}],\{left})")
  fact("tlsf_physical_ok(\{zero},65536,\{tail},[\{p},\{tail}],\{both})")
  fact("tlsf_free_covers(\{m},\{hd},\{p},\{both})")
  fact("(\{both})(\{tail}) == (\{hd})(\{tail})")
  for (model, level, slot) in [(released, 0, 0), (left, 1, 4), (both, 2, 0)] {
    let addr = if level == 0 { m } else { p }
    fact(
      "tlsf_level_of((\{model})(\{addr})) == \{level} && tlsf_slot_of((\{model})(\{addr})) == \{slot}",
    )
  }
  // Coalescing the final block transfers the last bit and the top address.
  for
    (lim, maddr, psize, msize) in [
      ("65536", "2200", "16", "63328"),
      ("4294967296", "4294967272", "4294965088", "16"),
    ] {
    let end = "(word(\{maddr}) : \{w})"
    let old = "(x : \{w}) => if x == \{p} { word(\{psize}) } else { word_or(word(\{msize}),word(3)) }"
    let merged = "tlsf_merge_headers(tlsf_release(\{old},\{end}),\{p},\{end})"
    fact("tlsf_physical_ok(\{zero},\{lim},\{end},[\{p},\{end}],\{old})")
    fact("tlsf_physical_ok(\{zero},\{lim},\{p},[\{p}],\{merged})")
    fact("tlsf_last((\{merged})(\{p})) && !tlsf_used((\{merged})(\{p}))")
    fact("tlsf_free_covers(\{end},\{old},\{p},\{merged})")
  }
}

///|
/// `t`, proved by computing it to true with `conv`.
fn computed(conv : @equal.Conv, t : @kernel.Term) -> @kernel.Thm raise {
  let th = conv(t)
  @bool.eqt_elim(th) catch {
    _ =>
      raise Failure(
        "not true by computation: " +
        @logic.show(t) +
        "\ncomputes to: " +
        @logic.show(@equal.rhs(@kernel.concl(th))),
      )
  }
}

///|
/// `th`, a statement `∀ xs, ...`, for the values `vals` of its variables
/// by name (a variable with no value stays).
fn instantiate(
  th : @kernel.Thm,
  vals : Map[String, @kernel.Term],
) -> @kernel.Thm raise {
  let (vars, _) = @basics.strip_forall(@kernel.concl(th))
  let args = vars
    .to_array()
    .map(fn(v) raise {
      match vals.get(@kernel.dest_var(v).0) {
        Some(t) => t
        None => v
      }
    })
  @bool.specl(@list.List(args), th)
}

///|
test "TLSF initialize page boundaries and the memory32 endpoint" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_initialize_pages", "tlsf_initialize_required", "tlsf_initialize_limit",
      "tlsf_initialize_origin", "tlsf_initialize_header", "tlsf_initialize_headers",
      "tlsf_initialize_valid", "tlsf_capacity_at", "tlsf_base", "tlsf_origin", "tlsf_physical_ok",
      "tlsf_layout", "tlsf_block_ok", "tlsf_coalesced", "tlsf_size", "tlsf_used",
      "tlsf_last",
    ].map(@logic.thm),
  )
  for
    (data_end, pages, origin, header) in [
      (0U, 1, 2176U, 63354U),
      (123U, 1, 2304U, 63226U),
      (63328U, 1, 65504U, 26U),
      (63329U, 2, 65520U, 65546U),
      (65536U, 2, 67712U, 63354U),
      (4294965088U, 65536, 4294967264U, 26U),
    ] {
    let limit = pages.to_int64() * 65536L
    let formulas = [
      "tlsf_initialize_pages((word(\{data_end}) : Word[32])) == \{pages}",
      "tlsf_initialize_required((word(\{data_end}) : Word[32])) == word(\{pages})",
      "tlsf_initialize_origin((word(\{data_end}) : Word[32])) == word(\{origin})",
      "tlsf_initialize_header((word(\{data_end}) : Word[32]),\{limit}) == word(\{header})",
      "tlsf_physical_ok((word(\{data_end}) : Word[32]),\{limit},word(\{origin}),[word(\{origin})],tlsf_initialize_headers(word(\{data_end}),\{limit}))",
    ]
    for formula in formulas {
      let th = conv(@logic.tm(formula))
      assert_true(@kernel.hyp(th).is_empty())
      assert_true(
        @basics.aconv(@equal.rhs(@kernel.concl(th)), @logic.tm("T")),
        msg=formula,
      )
    }
  }
  for
    formula in [
      "tlsf_initialize_valid((word(0) : Word[32]),0)", "tlsf_initialize_valid((word(65536) : Word[32]),65536)",
      "!tlsf_initialize_valid((word(65537) : Word[32]),65536)", "!tlsf_initialize_valid((word(0) : Word[32]),65535)",
      "!tlsf_initialize_valid((word(4294965089) : Word[32]),4294967296)", "tlsf_initialize_limit((word(0) : Word[32]),131072) == 131072",
    ] {
    let th = conv(@logic.tm(formula))
    assert_true(@kernel.hyp(th).is_empty())
    assert_true(
      @basics.aconv(@equal.rhs(@kernel.concl(th)), @logic.tm("T")),
      msg=formula,
    )
  }
}

///|
test "small-page slot geometry covers every size class and the memory32 endpoint" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_small_total", "tlsf_small_slot", "tlsf_small_slots", "tlsf_small_used",
    ].map(@tlsf.thm),
    suc=[("tlsf_small_slots", 3, 2)],
  )
  let fact = (s : String) => {
    let th = @bool.eqt_elim(conv(@logic.tm(s)))
    assert_true(@kernel.hyp(th).is_empty(), msg=s)
  }
  for index in 1..<33 {
    let size = index * 8
    let total = 1056 / (8 + size)
    fact("tlsf_small_total(\{size}) == \{total}")
    fact(
      "LENGTH(tlsf_small_slots((word(2176) : Word[32]),\{size},\{total})) == \{total}",
    )
    fact(
      "val(tlsf_small_slot((word(2176) : Word[32]),\{size},\{total-1}))+8+\{size} <= 3272",
    )
  }
  fact(
    "val(tlsf_small_slot((word(4294966200) : Word[32]),256,3)) == 4294967024",
  )
  fact(
    "val(tlsf_small_slot((word(4294966200) : Word[32]),256,3))+264 <= 4294967296",
  )
  fact(
    "tlsf_small_used([(word(2472) : Word[32])],[(word(2208) : Word[32])]) == 2",
  )
  fact("!(tlsf_small_used([(word(2472) : Word[32])],NIL) == 0)")
}

///|
test "small-page partitions reject duplicate missing foreign and shared slots" {
  @tlsf.load()
  let w = @logic.w32
  let p = "(word(2176) : \{w})"
  let live = "[(word(2208) : \{w})]"
  let cached = "[(word(2472) : \{w})]"
  let loc = "[(word(2736) : \{w}),word(3000)]"
  let conv = @wasm.compute_conv(
    ["tlsf_small_total", "tlsf_small_slot", "tlsf_small_slots", "tlsf_count"].map(
      @tlsf.thm,
    ) +
    [@lists.filter(), @lists.mem()],
    suc=[("tlsf_small_slots", 3, 2)],
  )
  for
    name in [
      "tlsf_small_example_partition", "tlsf_small_example_lists", "tlsf_small_example_backing",
    ] {
    assert_true(@kernel.hyp(@tlsf.thm(name)).is_empty(), msg=name)
  }
  for
    (bad_loc, bad_cached, bad_live, witness) in [
      ("[(word(2736) : \{w}),word(2736),word(3000)]", cached, live, "2736"),
      ("[(word(3000) : \{w})]", cached, live, "2736"),
      ("[(word(2736) : \{w}),word(4000)]", cached, live, "4000"),
      (loc, "[(word(2208) : \{w}),word(2472)]", live, "2208"),
    ] {
    let exact = @bool.ispecl(
      @list.List(
        [p, "256", bad_loc, bad_cached, bad_live, "(word(\{witness}) : \{w})"].map(
          @logic.tm,
        ),
      ),
      @tlsf.thm("tlsf_small_partition_counts"),
    )
    let rejected = @tactics.prove(
      @logic.tm(
        "!tlsf_small_partition(\{p},256,\{bad_loc},\{bad_cached},\{bad_live})",
      ),
      @logic.seq([@tactics.mp_tac(exact), @tactics.conv_tac(conv)]),
    )
    assert_true(@kernel.hyp(rejected).is_empty())
  }
}

///|
test "small-page lists reject wrong classes and premature page reclamation" {
  @tlsf.load()
  let w = @logic.w32
  let lw = "List[\{w}]"
  let p = "(word(2176) : \{w})"
  let sz = "(p : \{w}) => (256 : Num)"
  let loc = "(p : \{w}) => [(word(2736) : \{w}),word(3000)]"
  let cached = "(p : \{w}) => [(word(2472) : \{w})]"
  let live = "(p : \{w}) => [(word(2208) : \{w})]"
  let empty = "(j : Num) => (NIL : \{lw})"
  let fast = "(j : Num) => if j == 32 { [(word(2472) : \{w})] } else { (NIL : \{lw}) }"
  let partial = "(j : Num) => if j == 32 { [\{p}] } else { (NIL : \{lw}) }"
  let conv = @wasm.compute_conv(
    [
      "tlsf_small_used", "tlsf_small_total", "tlsf_count", "tlsf_used", "tlsf_size",
    ].map(@tlsf.thm) +
    [@lists.filter(), @lists.mem()],
  )
  let reject = (statement : String, rule : @kernel.Thm) => {
    let th = @tactics.prove(
      @logic.tm("!\{statement}"),
      @logic.seq([@tactics.mp_tac(rule), @tactics.conv_tac(conv)]),
    )
    assert_true(@kernel.hyp(th).is_empty(), msg=statement)
  }
  for
    bad_fast in [
      empty,
      "(j : Num) => if j == 31 { [(word(2472) : \{w})] } else { (NIL : \{lw}) }",
      "(j : Num) => if j == 32 { [(word(2472) : \{w}),word(2472)] } else { (NIL : \{lw}) }",
    ] {
    let rule = @bool.ispecl(
      @list.List(
        [
          "[\{p}]",
          sz,
          loc,
          cached,
          live,
          bad_fast,
          partial,
          p,
          "(word(2472) : \{w})",
        ].map(@logic.tm),
      ),
      @tlsf.thm("tlsf_small_cached_exact"),
    )
    reject(
      "tlsf_small_lists_ok([\{p}],\{sz},\{loc},\{cached},\{live},\{bad_fast},\{partial})",
      rule,
    )
  }
  let rule = @bool.ispecl(
    @list.List(["[\{p}]", sz, loc, cached, live, fast, empty, p].map(@logic.tm)),
    @tlsf.thm("tlsf_small_partial_exact"),
  )
  reject(
    "tlsf_small_lists_ok([\{p}],\{sz},\{loc},\{cached},\{live},\{fast},\{empty})",
    rule,
  )
  let full_cached = "(p : \{w}) => [(word(2208) : \{w}),word(2472),word(2736),word(3000)]"
  let no_live = "(p : \{w}) => (NIL : \{lw})"
  let rule = @bool.ispecl(
    @list.List(
      ["[\{p}]", sz, no_live, full_cached, no_live, fast, partial, p].map(
        @logic.tm,
      ),
    ),
    @tlsf.thm("tlsf_small_partial_exact"),
  )
  reject(
    "tlsf_small_lists_ok([\{p}],\{sz},\{no_live},\{full_cached},\{no_live},\{fast},\{partial})",
    rule,
  )
  for header in ["1090", "1027"] {
    let hd = "(p : \{w}) => (word(\{header}) : \{w})"
    let rule = @bool.ispecl(
      @list.List(
        ["[\{p}]", hd, "[\{p}]", sz, loc, cached, live, "65536", p].map(
          @logic.tm,
        ),
      ),
      @tlsf.thm("tlsf_small_backing_used"),
    )
    reject(
      "tlsf_small_backing([\{p}],\{hd},[\{p}],\{sz},\{loc},\{cached},\{live},65536)",
      rule,
    )
  }
}

///|
/// Sparse kernel execution avoids expanding a whole page into a deep byte
/// literal. Complete pages are also tested by the shipped-WAT runtime tests.
test "compiled Page initialization stores and null return preserve client bytes" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_pop_code", "tlsf_push_code", "tlsf_take_code", "tlsf_page_allocate_code",
      "tlsf_page_allocate_begin", "tlsf_page_allocate_step",
    ].map(@tlsf.thm),
  )
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let instance = "Inst(NIL,[0,1,2,3],NIL,[0],NIL,NIL,NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = value(
    "Wstore([Func_native(\{instance},Tf([T_num(T_i32)],NIL),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_pop_code(word(0))),Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_push_code(word(0))),Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_take_code(word(0),0,1)),Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),[T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32),T_num(T_i32)],tlsf_page_allocate_code(2))],NIL,[(Limit_t(0,NONE),(memory_bytes : List[Word[8]]))],NIL,NIL,NIL)",
  )
  let store = (bytes : Array[UInt32]) => {
    let mem = @lists.mk_list(
      @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
      @kernel.type_of(byte_terms[0]),
    )
    @kernel.vsubst(@list.List([(mem, memory_var)]), template)
  }
  let put = (bytes : Array[UInt32], addr : Int32, v : UInt32) => {
    for k in 0..<4 {
      bytes[addr + k] = (v >> (8 * k)) & 255U
    }
  }
  let locals = (xs : Array[Int32]) => {
    "[" + xs.map(x => "V_num(ConstInt32(word(\{x})))").join(",") + "]"
  }
  let check = (
    before : Array[UInt32],
    after : Array[UInt32],
    lc : Array[Int32],
    lc2 : Array[Int32],
    code : String,
    result : String,
  ) => {
    let frame = value("Wframe(\{locals(lc)},\{instance})")
    let final_frame = value("Wframe(\{locals(lc2)},\{instance})")
    let run = @wasm.run(
      @pair.mk_pair((store(before), @pair.mk_pair((frame, value(code))))),
    )
    assert_true(@kernel.hyp(run).is_empty())
    let expected = @pair.mk_pair(
      (store(after), @pair.mk_pair((final_frame, value(result)))),
    )
    assert_true(@basics.aconv(@kernel.rand(@kernel.concl(run)), expected))
  }
  let dirty = () => {
    Array::makei(104, n => (n * 19 + 7).reinterpret_as_uint() & 255U)
  }
  let before = dirty()
  put(before, 0, 0U)
  check(
    before,
    before,
    [123],
    [123],
    "[Basic(EConstNum(ConstInt32(word(256)))),Basic(Call(3))]",
    "[Basic(EConstNum(ConstInt32(word(0))))]",
  )
  for size in [8, 256] {
    let p = 32
    let before = dirty()
    let after = before.copy()
    let total = 1056 / (8 + size)
    put(after, p + 8, size.reinterpret_as_uint())
    put(after, p + 12, total.reinterpret_as_uint())
    put(after, p + 20, (p + 32).reinterpret_as_uint())
    put(after, p + 28, 0U)
    put(after, p + 32, 4U)
    put(after, p + 36, p.reinterpret_as_uint())
    put(after, p + 40, 0U)
    check(
      before,
      after,
      [size, p, 6, 7, 8, 9],
      [size, p, p + 32, 1, 8, total],
      "MAP(Basic,tlsf_page_allocate_begin(2))",
      "(NIL : List[Einstr])",
    )
  }
  let before = dirty()
  put(before, 52, 64U)
  put(before, 64, 4U)
  put(before, 68, 32U)
  put(before, 72, 0U)
  let after = before.copy()
  put(after, 52, 80U)
  put(after, 80, 4U)
  put(after, 84, 32U)
  put(after, 88, 64U)
  check(
    before,
    after,
    [8, 32, 64, 1, 9, 66],
    [8, 32, 80, 1, 80, 66],
    "MAP(Basic,tlsf_page_allocate_step(2))",
    "[Basic(EConstNum(ConstInt32(word(2))))]",
  )
}

///|
/// Run the exact inlined branch with a sparse partial page, then each
/// predecessor unlink path. Compare the whole endpoint, including all bytes
/// outside the explicitly changed allocator words.
test "compiled Block free release and unlink preserve other bytes" {
  @tlsf.load()
  let conv = @wasm.compute_conv([
    @tlsf.thm("tlsf_block_free_code"),
    @tlsf.thm("tlsf_block_free_release"),
    @tlsf.thm("tlsf_block_free_unlink_prev"),
    @tlsf.thm("tlsf_block_free_unlink_head"),
  ])
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let instance = "Inst(NIL,NIL,NIL,[0],NIL,NIL,NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = @logic.tm(
    "Wstore(NIL,NIL,[(Limit_t(0,NONE),(memory_bytes : List[Word[8]]))],NIL,NIL,NIL)",
  )
  let store = (bytes : Array[UInt32]) => {
    let mem = @lists.mk_list(
      @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
      @kernel.type_of(byte_terms[0]),
    )
    @kernel.vsubst(@list.List([(mem, memory_var)]), template)
  }
  let put = (bytes : Array[UInt32], addr : Int32, v : Int32) => {
    for k in 0..<4 {
      bytes[addr + k] = (v.reinterpret_as_uint() >> (8 * k)) & 255U
    }
  }
  let locals = (xs : Array[Int32]) => {
    "[" + xs.map(x => "V_num(ConstInt32(word(\{x})))").join(",") + "]"
  }
  let check = (
    before : Array[UInt32],
    after : Array[UInt32],
    lc : Array[Int32],
    lc2 : Array[Int32],
    code : String,
    result : String,
  ) => {
    let run = @wasm.run(
      @pair.mk_pair(
        (
          store(before),
          @pair.mk_pair(
            (
              value("Wframe(\{locals(lc)},\{instance})"),
              value("MAP(Basic,\{code})"),
            ),
          ),
        ),
      ),
    )
    assert_true(@kernel.hyp(run).is_empty())
    let expected = @pair.mk_pair(
      (
        store(after),
        @pair.mk_pair(
          (value("Wframe(\{locals(lc2)},\{instance})"), value(result)),
        ),
      ),
    )
    assert_true(@basics.aconv(@kernel.rand(@kernel.concl(run)), expected))
  }
  let zero = "[Basic(EConstNum(ConstInt32(word(0))))]"
  for head in [0, 64] {
    for whole in [false, true] {
      let before = Array::makei(128, n => {
        (n * 37 + 11).reinterpret_as_uint() & 255U
      })
      put(before, 44, 4)
      put(before, 48, 2)
      put(before, 52, head)
      put(before, 84, 32)
      let after = before.copy()
      put(after, 48, 1)
      put(after, 52, 80)
      put(after, 88, head)
      check(
        before,
        after,
        [123, 80, 9],
        [32, 2, 9],
        if whole {
          "tlsf_block_free_code(word(0),0)"
        } else {
          "tlsf_block_free_release(word(0),0)"
        },
        if whole {
          zero
        } else {
          "(NIL : List[Einstr])"
        },
      )
    }
  }
  for has_prev in [false, true] {
    for nx in [0, 96] {
      let before = Array::makei(128, n => {
        (n * 29 + 17).reinterpret_as_uint() & 255U
      })
      let prev = if has_prev { 64 } else { 0 }
      put(before, 40, 0)
      put(before, 56, prev)
      put(before, 60, nx)
      put(before, if has_prev { 92 } else { 12 }, 32)
      if nx != 0 {
        put(before, nx + 24, 32)
      }
      let after = before.copy()
      put(after, if has_prev { 92 } else { 12 }, nx)
      if nx != 0 {
        put(after, nx + 24, prev)
      }
      // The isolated head-path test deliberately wraps the table address
      // into this sparse memory. The full invariant tests use a real table.
      check(
        before,
        after,
        [32, if has_prev { 56 } else { 0 }, 9],
        [32, nx, 0 + prev],
        if has_prev {
          "tlsf_block_free_unlink_prev(word(0),0)"
        } else {
          "tlsf_block_free_unlink_head(word(4294965392),0)"
        },
        zero,
      )
    }
  }
}

///|
test "Block free models full partial last and cached pages" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_block_free_loc", "tlsf_block_free_live", "tlsf_block_free_pages", "tlsf_block_free_partial",
      "tlsf_small_put", "tlsf_small_put_class", "tlsf_small_remove", "tlsf_small_used",
      "tlsf_small_total",
    ].map(@tlsf.thm) +
    [@lists.filter()],
  )
  let w = @logic.w32
  let lw = "List[\{w}]"
  let p = "(word(32) : \{w})"
  let b = "(word(64) : \{w})"
  let pages = "[\{p},word(2048)]"
  let size = "(q : \{w}) => (256 : Num)"
  let local_slots = "(q : \{w}) => ([word(592)] : \{lw})"
  for
    (live, cached, before_partial, expected_pages, expected_partial) in [
      (
        "[word(64),word(328),word(592),word(856)]", "NIL", "[word(2048)]", pages,
        "[word(32),word(2048)]",
      ),
      (
        "[word(64),word(328)]", "NIL", "[word(32),word(2048)]", pages, "[word(32),word(2048)]",
      ),
      // A cached slot is still counted, so the last live slot cannot reclaim it.
      (
        "[word(64)]", "[word(328)]", "[word(32),word(2048)]", pages, "[word(32),word(2048)]",
      ),
      (
        "[word(64)]", "NIL", "[word(2048),word(32)]", "[word(2048)]", "[word(2048)]",
      ),
    ] {
    let live = "(q : \{w}) => ((\{live}) : \{lw})"
    let cached = "(q : \{w}) => ((\{cached}) : \{lw})"
    let pre_part = "(j : Num) => (if j == 32 { (\{before_partial} : \{lw}) } else { (NIL : \{lw}) })"
    let claim = "tlsf_block_free_loc(\{local_slots},\{p},\{b},\{p}) == [word(64),word(592)] && tlsf_block_free_live(\{live},\{p},\{b},\{p}) == tlsf_small_remove(\{b},(\{live})(\{p})) && tlsf_block_free_live(\{live},\{p},\{b},word(2048)) == (\{live})(word(2048)) && tlsf_block_free_pages(\{pages},\{cached},\{live},\{p}) == (\{expected_pages} : \{lw}) && tlsf_block_free_partial(\{pre_part},\{size},\{cached},\{live},\{p},32) == (\{expected_partial} : \{lw})"
    let proof = computed(conv, @logic.tm(claim))
    assert_true(@kernel.hyp(proof).is_empty())
  }
  assert_true(@kernel.hyp(@tlsf.thm("tlsf_block_free_all")).is_empty())
}

///|
/// Compare the complete store after the exact publication prefixes. These
/// sparse word-path fixtures wrap the linked table base into 128 bytes;
/// shipped-WAT runtime tests exercise the actual non-wrapping invariant.
test "compiled page publication updates metadata and preserves every other byte" {
  @tlsf.load()
  let conv = @wasm.compute_conv(
    [
      "tlsf_page_publish_fresh_code", "tlsf_page_publish_partial_code", "tlsf_page_publish_head_code",
    ].map(@tlsf.thm),
  )
  let value = (s : String) => @equal.rhs(@kernel.concl(conv(@logic.tm(s))))
  let instance = "Inst(NIL,NIL,NIL,[0],NIL,NIL,NIL)"
  let byte_terms = Array::makei(256, n => @logic.tm("(word(\{n}) : Word[8])"))
  let memory_var = @logic.tm("(memory_bytes : List[Word[8]])")
  let template = @logic.tm(
    "Wstore(NIL,NIL,[(Limit_t(0,NONE),(memory_bytes : List[Word[8]]))],NIL,NIL,NIL)",
  )
  let store = (bytes : Array[UInt32]) => {
    @kernel.vsubst(
      @list.List([
        (
          @lists.mk_list(
            @list.List(bytes.map(x => byte_terms[x.reinterpret_as_int()])),
            @kernel.type_of(byte_terms[0]),
          ),
          memory_var,
        ),
      ]),
      template,
    )
  }
  let put = (bytes : Array[UInt32], addr : Int32, x : UInt32) => {
    for k in 0..<4 {
      bytes[addr + k] = (x >> (8 * k)) & 255U
    }
  }
  let lc = (xs : Array[Int32]) => {
    "[" + xs.map(x => "V_num(ConstInt32(word(\{x})))").join(",") + "]"
  }
  let check = (
    before : Array[UInt32],
    after : Array[UInt32],
    locals : Array[Int32],
    outlocals : Array[Int32],
    code : String,
    result : Int32,
  ) => {
    let run = @wasm.run(
      @pair.mk_pair(
        (
          store(before),
          @pair.mk_pair(
            (
              value("Wframe(\{lc(locals)},\{instance})"),
              value("MAP(Basic,\{code})"),
            ),
          ),
        ),
      ),
    )
    assert_true(@kernel.hyp(run).is_empty())
    let final_frame = value("Wframe(\{lc(outlocals)},\{instance})")
    let final_code = value("[Basic(EConstNum(ConstInt32(word(\{result}))))]")
    let expected = @pair.mk_pair(
      (store(after), @pair.mk_pair((final_frame, final_code))),
    )
    assert_true(
      @basics.aconv(@kernel.rand(@kernel.concl(run)), expected),
      msg=code,
    )
  }
  for size in [8, 256] {
    let off = (1912 + size) % 16
    let d = 0U - ((1912 + size) / 16 * 16).reinterpret_as_uint()
    for next in [0, 104] {
      let before = Array::makei(128, n => {
        (n * 31 + 9).reinterpret_as_uint() & 255U
      })
      put(before, off, 0U)
      put(before, 44, (1056 / (8 + size)).reinterpret_as_uint())
      put(before, 52, 80U)
      put(before, 88, next.reinterpret_as_uint())
      let after = before.copy()
      put(after, off, next.reinterpret_as_uint())
      put(after, 48, (1056 / (8 + size)).reinterpret_as_uint())
      put(after, 52, 0U)
      put(after, 88, 0U)
      check(
        before,
        after,
        [32, 80, size, 52, 9],
        [32, 88, size, 52, next],
        "tlsf_page_publish_fresh_code(word(\{d}))",
        88,
      )
      check(
        before,
        before,
        [32, 9, size, 7, 6],
        [32, 80, size, 52, 6],
        "tlsf_page_publish_head_code(word(\{d}))",
        80,
      )
      for next_page in [0, 96] {
        let before = before.copy()
        put(before, off + 4, 32U)
        put(before, 48, 1U)
        put(before, 56, 0U)
        put(before, 60, next_page.reinterpret_as_uint())
        if next_page != 0 {
          put(before, next_page + 24, 32U)
        }
        let after = before.copy()
        put(after, off, next.reinterpret_as_uint())
        put(after, off + 4, next_page.reinterpret_as_uint())
        put(after, 48, (1056 / (8 + size)).reinterpret_as_uint())
        put(after, 52, 0U)
        put(after, 88, 0U)
        if next_page != 0 {
          put(after, next_page + 24, 0U)
        }
        check(
          before,
          after,
          [32, 7, size, 9, 6],
          [next_page, 80, size, 52, next],
          "tlsf_page_publish_partial_code(word(\{d}))",
          88,
        )
      }
    }
  }
}

///|
test "compiled allocation entry theorems are closed and cover growth and retry" {
  @tlsf.load()
  @testkit.check_axioms()
  // Ground the native-closure premises in a concrete function table. This
  // checks that closing the entry theorems did not make their premises false.
  let instance = "Inst(NIL,[0,1,2,3,4,5,6],NIL,[0],NIL,NIL,NIL)"
  let i32 = "T_num(T_i32)"
  let closure = (result : String, count : Int32, code : String) => {
    "Func_native(" +
    instance +
    ",Tf([" +
    i32 +
    "]," +
    result +
    "),[" +
    Array::make(count, i32).join(",") +
    "]," +
    code +
    ")"
  }
  let fs = "[" +
    [
      closure("NIL", 4, "tlsf_pop_code(word(0))"),
      closure("[" + i32 + "]", 3, "tlsf_push_code(word(0))"),
      closure("[" + i32 + "]", 5, "tlsf_take_code(word(0),0,1)"),
      closure("[" + i32 + "]", 5, "tlsf_page_allocate_code(2)"),
      closure("[" + i32 + "]", 1, "tlsf_ensure_code(word(0),0,1)"),
      closure("[" + i32 + "]", 4, "tlsf_try_malloc_code(word(0),7,3,2)"),
      closure("[" + i32 + "]", 5, "tlsf_full_malloc_code(word(0),7,3,2,4)"),
    ].join(",") +
    "]"
  let substitutions = [
      (@logic.tm(fs), @logic.tm("(fs : List[Cl])")),
      (@logic.tm(instance), @logic.tm("(inst : Inst)")),
      (@logic.tm("(word(0) : Word[32])"), @logic.tm("(d : Word[32])")),
    ] +
    [
      ("pop", 0),
      ("push", 1),
      ("take_idx", 2),
      ("page_idx", 3),
      ("ensure_idx", 4),
      ("try_idx", 5),
      ("full_idx", 6),
      ("initialize_idx", 7),
    ].map(pair => {
      let (name, value) = pair
      (@logic.tm(value.to_string()), @logic.tm("(" + name + " : Num)"))
    })
  let conv = @wasm.compute_conv([])
  for name in ["tlsf_try_malloc_all", "tlsf_full_malloc_all"] {
    let body = @basics.strip_forall(@kernel.concl(@tlsf.thm(name))).1
    let bindings = @kernel.vsubst(
      @list.List(substitutions),
      @basics.dest_imp(body).0,
    )
    let checked = conv(bindings)
    assert_true(@kernel.hyp(checked).is_empty(), msg=name)
    assert_true(
      @basics.aconv(@equal.rhs(@kernel.concl(checked)), @logic.tm("T")),
      msg=name,
    )
  }

  for
    name in [
      "tlsf_try_malloc_body", "tlsf_try_malloc_specs", "tlsf_try_malloc_all", "tlsf_try_malloc_run",
      "tlsf_malloc_first_block", "tlsf_malloc_retry_block", "tlsf_malloc_full_growth_all",
      "tlsf_full_malloc_fast_all", "tlsf_full_malloc_slow_body", "tlsf_full_malloc_slow_call",
      "tlsf_full_malloc_all", "tlsf_full_malloc_run", "tlsf_malloc_frame_state",
      "tlsf_malloc_result_original_frame",
    ] {
    let theorem = @tlsf.thm(name)
    assert_true(@kernel.hyp(theorem).is_empty(), msg=name)
    let constants = @wasm.term_constants(@kernel.concl(theorem))
    if name.has_suffix("_all") || name.has_suffix("_run") {
      assert_false(constants.contains("specs_ok"), msg=name)
    }
    if name.has_suffix("_run") {
      for triple in ["sl_triple_m", "sl_triple_g", "sl_abort_m"] {
        assert_false(constants.contains(triple), msg=name)
      }
    }
  }
  assert_true(
    @wasm.term_constants(@kernel.concl(@tlsf.thm("tlsf_try_malloc_run"))).contains(
      "reduce_trans",
    ),
  )
  let full = @wasm.term_constants(
    @kernel.concl(@tlsf.thm("tlsf_full_malloc_run")),
  )
  assert_true(full.contains("reduce_trans"))
  assert_true(full.contains("Trap"))
  assert_true(full.contains("tlsf_malloc_state"))
  assert_true(full.contains("tlsf_full_malloc_post"))
}

///|
/// Run the actual native closures, including full_malloc's result block and
/// early return. A zero request must leave the store and caller locals exact.
test "compiled try and full malloc return zero without touching any byte" {
  @tlsf.load()
  let conv = @wasm.compute_conv([
    @tlsf.thm("tlsf_try_malloc_code"),
    @tlsf.thm("tlsf_full_malloc_code"),
  ])
  let value = (source : String) => {
    @equal.rhs(@kernel.concl(conv(@logic.tm(source))))
  }
  let instance = "Inst(NIL,[0],NIL,[0],NIL,NIL,NIL)"
  let frame = value(
    "Wframe([V_num(ConstInt32(word(123))),V_num(ConstInt32(word(456)))],\{instance})",
  )
  let code = value(
    "[Basic(EConstNum(ConstInt32((word(0) : Word[32])))),Basic(Call(0))]",
  )
  for
    (name, count, arguments) in [
      ("tlsf_try_malloc_code", 4, "word(0),0,0,0"),
      ("tlsf_full_malloc_code", 5, "word(0),0,0,0,0"),
    ] {
    let locals = "[" + Array::make(count, "T_num(T_i32)").join(",") + "]"
    let store = value(
      "Wstore([Func_native(\{instance},Tf([T_num(T_i32)],[T_num(T_i32)]),\{locals},\{name}(\{arguments}))],NIL,[(Limit_t(0,NONE),[(word(17) : Word[8]),word(29),word(83),word(251)])],NIL,NIL,NIL)",
    )
    let cfg = @pair.mk_pair((store, @pair.mk_pair((frame, code))))
    let theorem = @wasm.run(cfg)
    assert_true(@kernel.hyp(theorem).is_empty(), msg=name)
    let (after, rest) = @pair.dest_pair(@kernel.rand(@kernel.concl(theorem)))
    let (after_frame, instructions) = @pair.dest_pair(rest)
    assert_true(@basics.aconv(after, store), msg=name)
    assert_true(@basics.aconv(after_frame, frame), msg=name)
    assert_true(
      @basics.aconv(
        instructions,
        @logic.tm("[Basic(EConstNum(ConstInt32((word(0) : Word[32]))))]"),
      ),
      msg=name,
    )
  }
}
