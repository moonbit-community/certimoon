// Arrays of i32 words in linear memory.
//
// - words_bytes(xs): the bytes of the words xs, each serialise_i32;
//   arr(a, xs) == pts(a, words_bytes(xs)), the words xs from address a.
// - arr_split, arr_cons: an array is its parts side by side.
// - arr_focus: the array ys ++ [x] ++ zs is x's bytes at a + 4 * LENGTH(ys)
//   beside the rest, so i32.load and i32.store reach that element.
// - st_arr_store, st_arr_load: those rules on exact states whose R is
//   star(arr(a, ...), fp(gs)), with the array split at the element.

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
  let frame = "(vs0 : List[Value]) => (ls : List[Value]) => (gs : List[Value]) => (h : \{heap}) => vs0 == (v : List[Value]) && ls == (l : List[Value]) && star(star(arr((a : Num), (ys : List[\{w}])), arr(a + 4 * LENGTH(ys) + 4, (zs : List[\{w}]))), (fp : \{rty})(gs), h)"
  let array = (elem : String) => "(gs : List[Value]) => (h : \{heap}) => star(arr(a, APPEND(ys, CONS(\{elem}, zs))), fp(gs), h)"
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
}
