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
