// Arrays of i32 words in linear memory.
//
// - words_bytes(xs): the bytes of the words xs, each serialise_i32;
//   arr(a, xs) == pts(a, words_bytes(xs)), the words xs from address a.
// - arr_split, arr_cons: an array is its parts side by side.
// - arr_focus: the array ys ++ [x] ++ zs is x's bytes at a + 4 * LENGTH(ys)
//   beside the rest, so i32.load and i32.store reach that element.
// - st_arr_store, st_arr_load: those rules on exact states whose R is
//   star(arr(a, ...), fp(gs, ms)), with the array split at the element.

///|
fn prove_array_rules() -> Unit raise {
  // the program logic's loads use it; examples.mbt used to prove it
  let roundtrip = prove_roundtrip()
  let w = w32
  let star = thm("star")
  let star_assoc = thm("star_assoc")
  let ser_len = thm("serialise_i32_length")
  def(
    "words_bytes",
    "words_bytes((NIL : List[\{w}])) == (NIL : List[\{w8}]) && words_bytes(CONS((x : \{w}), xs)) == APPEND(serialise_i32(x), words_bytes(xs))",
  )
  def("arr", "arr(a, (xs : List[\{w}])) == pts(a, words_bytes(xs))")
  let words_bytes = thm("words_bytes")
  let arr = thm("arr")
  let wb_append = lemma(
    "words_bytes_append",
    "∀ xs : List[\{w}], ∀ ys : List[\{w}], words_bytes(APPEND(xs, ys)) == APPEND(words_bytes(xs), words_bytes(ys))",
    seq([
      @lists.list_induct_tac,
      @simp.asm_rewrite_tac(ths([words_bytes, @lists.append(), @lists.append_assoc()])),
    ]),
  )
  let wb_length = lemma(
    "length_words_bytes",
    "∀ xs : List[\{w}], LENGTH(words_bytes(xs)) == 4 * LENGTH(xs)",
    seq([
      @lists.list_induct_tac,
      @simp.asm_rewrite_tac(ths([words_bytes, @lists.length(), @lists.length_append(), ser_len])),
      @tactics.try_tac(@int.arith_tac),
    ]),
  )
  let _ = lemma(
    "arr_split",
    "∀ a : Num, ∀ xs : List[\{w}], ∀ ys : List[\{w}], arr(a, APPEND(xs, ys)) == star(arr(a, xs), arr(a + 4 * LENGTH(xs), ys))",
    @simp.rewrite_tac(ths([arr, wb_append, thm("pts_split"), wb_length])),
  )
  let arr_cons = lemma(
    "arr_cons",
    "∀ a : Num, ∀ x : \{w}, ∀ xs : List[\{w}], arr(a, CONS(x, xs)) == star(pts(a, serialise_i32(x)), arr(a + 4, xs))",
    @simp.rewrite_tac(ths([arr, words_bytes, thm("pts_split"), ser_len])),
  )
  let left_comm = lemma(
    "star_left_comm",
    "∀ p : \{hprop}, ∀ q : \{hprop}, ∀ r : \{hprop}, star(p, star(q, r)) == star(q, star(p, r))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([@equal.gsym(star_assoc)])),
      @tactics.subst1_tac(@bool.ispecl(@list.List([tm("(p : \{hprop})"), tm("(q : \{hprop})")]), thm("star_comm"))),
      @simp.rewrite_tac(ths([])),
    ]),
  )
  let arr_focus = lemma(
    "arr_focus",
    "∀ a : Num, ∀ ys : List[\{w}], ∀ x : \{w}, ∀ zs : List[\{w}], arr(a, APPEND(ys, CONS(x, zs))) == star(pts(a + 4 * LENGTH(ys), serialise_i32(x)), star(arr(a, ys), arr(a + 4 * LENGTH(ys) + 4, zs)))",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @simp.rewrite_tac(ths([thm("arr_split"), arr_cons])),
      @tactics.match_accept_tac(left_comm),
    ]),
  )
  let star_pure_r = lemma(
    "star_pure_r",
    "∀ c : Bool, ∀ p : \{hprop}, ∀ r : \{hprop}, ∀ h : \{heap}, star(p, (h1 : \{heap}) => c && r(h1), h) == (c && star(p, r, h))",
    seq([@simp.rewrite_tac(ths([star])), @meson.meson_tac(ths([]))]),
  )
  // the array rules, from sl_store_i32 and sl_load_i32 with the rest of
  // the array (and the stack and locals) as the frame
  let frame = "(vs0 : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{heap}) => vs0 == (v : List[Value]) && ls == (l : List[Value]) && star(star(arr((a : Num), (ys : List[\{w}])), arr(a + 4 * LENGTH(ys) + 4, (zs : List[\{w}]))), (fp : \{rty})(gs, ms), h)"
  let array = (elem : String) => "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => star(arr(a, APPEND(ys, CONS(\{elem}, zs))), fp(gs, ms), h)"
  let vars = "∀ v : List[Value], ∀ l : List[Value], ∀ a : Num, ∀ ys : List[\{w}], ∀ x0 : \{w}, ∀ zs : List[\{w}], ∀ fp : \{rty}, ∀ k : \{w}, ∀ al : Num, ∀ off : Num"
  // the element's address, as the rule's hypothesis says
  let at = @kernel.assume_rule(tm("val((k : \{w})) + (off : Num) == (a : Num) + 4 * LENGTH((ys : List[\{w}]))"))
  let ent = seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths([thm("st"), star_pure_r, @class.eta_ax()])),
    @tactics.repeat_tac(@tactics.strip_tac),
    subst_vars(),
    @tactics.try_tac(@tactics.exists_tac(tm("(v : List[Value])"))),
    @tactics.rule_assum_tac(@simp.rewrite_rule(ths([arr_focus, star_assoc, at]))),
    @simp.rewrite_tac(ths([arr_focus, star_assoc, star_pure_r, @class.eta_ax(), roundtrip, at])),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let array_rule = (name : String, stmt : String, base : String, args : Array[String]) => {
    let inst = @bool.ispecl(@list.List(args.map(tm)), thm(base))
    let (_, triple) = @basics.dest_imp(@kernel.concl(inst))
    let (_, parts) = @basics.strip_comb(triple)
    guard parts.to_array() is [p, _, q] else { raise Failure("array_rule: " + base) }
    lemma(
      name,
      stmt,
      seq([
        @tactics.repeat_tac(@tactics.strip_tac),
        @tactics.match_mp_tac(thm("sl_conseq")),
        @tactics.exists_tac(p),
        @tactics.exists_tac(q),
        @tactics.repeat_tac(@tactics.conj_tac),
        @tactics.first(@list.List([
          solve(seq([@tactics.match_mp_tac(inst), @simp.rewrite_tac(ths([ser_len]))])),
          solve(ent),
        ])),
      ]),
    )
  }
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let _ = array_rule(
    "st_arr_store",
    "\{vars}, ∀ x : \{w}, val(k) + off == a + 4 * LENGTH(ys) → sl_triple(st(APPEND(v, [\{i("k")}, \{i("x")}]), l, \{array("x0")}), [Store(T_i32, NONE, al, off)], st(v, l, \{array("x")}))",
    "sl_store_i32",
    [frame, "(k : \{w})", "(al : Num)", "(off : Num)", "(x : \{w})", "serialise_i32((x0 : \{w}))"],
  )
  let _ = array_rule(
    "st_arr_load",
    "\{vars}, val(k) + off == a + 4 * LENGTH(ys) → sl_triple(st(APPEND(v, [\{i("k")}]), l, \{array("x0")}), [Load(T_i32, NONE, al, off)], st(APPEND(v, [\{i("x0")}]), l, \{array("x0")}))",
    "sl_load_i32",
    [frame, "(k : \{w})", "(al : Num)", "(off : Num)", "serialise_i32((x0 : \{w}))"],
  )
  prove_array_at_rules()
}

///|
/// The array rules by index: the whole array arr(val(P), xs) in R, and the
/// element at P + 4J, which i32.load reads as EL(val(J), xs) and i32.store
/// writes with list_update. From st_arr_load and st_arr_store, with the
/// array split at the element (split_at).
fn prove_array_at_rules() -> Unit raise {
  let w = w32
  let val_lemmas = [@words.val_word_add(), @words.val_word_mul(), @words.val_word(), @words.dimindex_32()]
  let addr_at = lemma(
    "addr_at",
    "∀ P : \{w}, ∀ J : \{w}, ∀ N : Num, val(P) + 4 * N < 4294967296 && val(J) < N → val(word_add(P, word_mul(J, word(4)))) + 0 == val(P) + 4 * val(J)",
    seq([
      @tactics.repeat_tac(@tactics.gen_tac),
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      have("val((J : \{w})) * 4 < 4294967296", @int.asm_arith_tac),
      have("val((P : \{w})) + val((J : \{w})) * 4 < 4294967296", @int.asm_arith_tac),
      @simp.rewrite_tac(ths(val_lemmas)),
      @tactics.conv_tac(@calc_num.num_reduce_conv),
      @simp.asm_simp_tac(ths([@arith.mod_lt()])),
      @int.asm_arith_tac,
    ]),
  )
  let i = (x : String) => "V_num(ConstInt32(\{x}))"
  let vars = "∀ v : List[Value], ∀ l : List[Value], ∀ P : \{w}, ∀ xs : List[\{w}], ∀ fp : \{rty}, ∀ J : \{w}, ∀ al : Num"
  let whole = (xs : String) => "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => star(arr(val(P), \{xs}), fp(gs, ms), h)"
  let k = i("word_add(P, word_mul(J, word(4)))")
  let hyp = "val(P) + 4 * LENGTH(xs) < 4294967296 && val(J) < LENGTH(xs)"
  let split = "LENGTH((vi : List[\{w}])) == val((J : \{w}))"
  let xs_eq = "(xs : List[\{w}]) == APPEND((vi : List[\{w}]), CONS(EL(val((J : \{w})), xs), (vs : List[\{w}])))"
  let at_tac = (base : String) => seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    have(
      "∃ vi : List[\{w}], ∃ vs : List[\{w}], \{split} && \{xs_eq}",
      seq([@tactics.match_mp_tac(thm("split_at")), @tactics.first_assum(th => @tactics.accept_tac(th))]),
    ),
    @tactics.first_x_assum(th => @tactics.strip_assume_tac(th)),
    // the array as vi ++ [its element] ++ vs, and the index as LENGTH(vi)
    @tactics.undisch_then(tm(xs_eq), th => @simp.once_rewrite_tac(ths([th]))),
    @tactics.undisch_then(tm(split), th => seq([
      @tactics.assume_tac(th),
      @simp.rewrite_tac(ths([@equal.gsym(th), thm("el_split"), thm("list_update_split")])),
    ])),
    @tactics.match_mp_tac(thm(base)),
    @simp.asm_rewrite_tac(ths([])),
    @tactics.match_mp_tac(addr_at),
    @tactics.exists_tac(tm("LENGTH((xs : List[\{w}]))")),
    @simp.asm_rewrite_tac(ths([])),
  ])
  let _ = lemma(
    "st_arr_load_at",
    "\{vars}, \{hyp} → sl_triple(st(APPEND(v, [\{k}]), l, \{whole("xs")}), [Load(T_i32, NONE, al, 0)], st(APPEND(v, [\{i("EL(val(J), xs)")}]), l, \{whole("xs")}))",
    at_tac("st_arr_load"),
  )
  let _ = lemma(
    "st_arr_store_at",
    "\{vars}, ∀ x : \{w}, \{hyp} → sl_triple(st(APPEND(v, [\{k}, \{i("x")}]), l, \{whole("xs")}), [Store(T_i32, NONE, al, 0)], st(v, l, \{whole("list_update(xs, val(J), x)")}))",
    at_tac("st_arr_store"),
  )
}
