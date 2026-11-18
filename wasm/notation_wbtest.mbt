///|
fn notation_words() -> Unit {
  @lib.verbose.val = false
  @preterm.type_invention_warning.val = false
  @words.load()
}

///|
fn word_render(source : String) -> @render.Statement raise {
  notation_words()
  let t = @term_syntax.parse_term(source)
  let shown = @render.statement(
    t,
    abbreviate=abbreviate_types,
    infixes=word_infixes(t),
    atoms=word_literals(t),
  )
  assert_eq(
    shown.canonical,
    @render.layout_statement(t, abbreviate=abbreviate_types),
  )
  shown
}

///|
test "word arithmetic and masks use infix notation with their width" {
  let shown = word_render(
    "∀ d : Word[32], word_add(word_and(word_add(d, word(15)), word(4294967280)), word(4)) == d",
  )
  inspect(
    shown.text,
    content=(
      #|∀ (d : W32), ((d +₃₂ 15w &₃₂ 4294967280w) +₃₂ 4w) == d
    ),
  )
  assert_true(shown.text.contains("+₃₂"))
  assert_true(shown.text.contains("&₃₂"))
  assert_false(shown.text.contains("word_add("))
  assert_false(shown.text.contains("word_and("))
  assert_false(shown.text.contains("(word :"))
  assert_eq(shown.references.length(), 6)
  assert_true(
    shown.references
    .iter()
    .all(r => ["word_add", "word_and", "word"].contains(r.constant)),
  )
}

///|
test "word notation preserves subtraction grouping and arithmetic precedence" {
  inspect(
    word_render(
      "∀ a : Word[32], ∀ b : Word[32], ∀ c : Word[32], word_sub(a, word_sub(b, c)) == a",
    ).text,
    content=(
      #|∀ (a b c : W32), (a −₃₂ (b −₃₂ c)) == a
    ),
  )
  inspect(
    word_render(
      "∀ a : Word[32], ∀ b : Word[32], ∀ c : Word[32], word_mul(word_add(a, b), c) == a",
    ).text,
    content=(
      #|∀ (a b c : W32), ((a +₃₂ b) ×₃₂ c) == a
    ),
  )
}

///|
test "nested word conversions containing notation stay compact" {
  let nested = word_render(
    "∀ hd : Word[32], word_sub(word(27), word(word_clz(word_and(hd, word(4294967292))))) == hd",
  )
  inspect(
    nested.text,
    content=(
      #|∀ (hd : W32), (27w −₃₂ word(word_clz((hd &₃₂ 4294967292w)))) == hd
    ),
  )
  assert_false(nested.text.contains("(word :"))
  assert_false(nested.text.contains("(word_clz :"))
}

///|
test "word notation supports different type instances and masked shifts" {
  let shown = word_render(
    "∀ a : Word[8], ∀ b : Word[64], ∀ c : Word[N], word_and(a, a) == a && word_or(b, b) == b && word_xor(c, c) == c",
  )
  inspect(
    shown.text,
    content=(
      #|∀ (a : Byte) (b : W64) (c : Word[N]),
      #|  (a &₈ a) == a && (b |₆₄ b) == b && (c ^ʷ c) == c
    ),
  )
  assert_true(shown.text.contains("&₈"))
  assert_true(shown.text.contains("|₆₄"))
  assert_true(shown.text.contains("^ʷ"))
  let shifts = word_render(
    "∀ a : Word[32], word_jshl(a, a) == word_jshr(a, word_jushr(a, a))",
  )
  inspect(
    shifts.text,
    content=(
      #|∀ (a : W32), (a <<₃₂ a) == (a >>₃₂ (a >>>₃₂ a))
    ),
  )
  assert_eq(shifts.references.map(r => r.constant), [
    "word_jshl", "word_jshr", "word_jushr",
  ])
}

///|
test "word notation leaves numeric arithmetic and shadowed variables alone" {
  notation_words()
  for
    source in [
      "∀ n : Num, n + 1 == 1 + n", "∀ word_add : (Word[32], Word[32]) -> Word[32], ∀ a : Word[32], word_add(a, a) == a",
    ] {
    let t = @term_syntax.parse_term(source)
    assert_true(word_infixes(t).is_empty())
    assert_eq(
      @render.statement(t, infixes=word_infixes(t)).text,
      @render.layout_statement(t),
    )
  }
}

///|
test "word notation accepts internal width types without a standalone spelling" {
  notation_words()
  let operator = @kernel.mk_const("word_add", List([]))
  let variable = @kernel.tyvars(@kernel.type_of(operator)).to_array()[0]
  let internal = @kernel.mk_vartype("internal-width")
  let instance = @kernel.inst(List([(internal, variable)]), operator)
  let rules = word_infixes(instance)
  assert_eq(rules.length(), 1)
  assert_eq(rules[0].symbol, "+ʷ")
}

///|
test "word literals preserve exact numeral values across widths" {
  let shown = word_render(
    "∀ a : Word[8], ∀ b : Word[32], ∀ c : Word[64], ∀ d : Word[N], a == word(32) && b == word(32) && c == word(18446744073709551617) && d == word(0)",
  )
  inspect(
    shown.text,
    content=(
      #|∀ (a : Byte) (b : W32) (c : W64) (d : Word[N]),
      #|  a == 32w && b == 32w && c == 18446744073709551617w && d == 0w
    ),
  )
  assert_true(shown.text.contains("32w"))
  assert_true(shown.text.contains("0w"))
  assert_true(shown.text.contains("18446744073709551617w"))
  assert_false(shown.text.contains("word("))
  assert_eq(shown.references.length(), 4)
  assert_true(shown.references.iter().all(r => r.constant == "word"))
}

///|
test "computed word conversions remain explicit and numeric literals stay numeric" {
  let shown = word_render(
    "∀ d : Word[32], ∀ n : Num, d == word(n) && d == word(16 + 16) && d == word(32) && n == 32",
  )
  inspect(
    shown.text,
    content=(
      #|∀ (d : W32) (n : Num), d == word(n) && d == word(16 + 16) && d == 32w && n == 32
    ),
  )
  assert_true(shown.text.contains("word(n)"))
  assert_true(shown.text.contains("word(16 + 16)"))
  assert_true(shown.text.contains("32w"))
  assert_true(shown.text.contains("n == 32"))
  assert_eq(shown.references.length(), 1)
  notation_words()
  for
    source in [
      "∀ word : (Num) -> Word[32], ∀ d : Word[32], word(32) == d", "(word : (Num) -> Word[32])",
    ] {
    let t = @term_syntax.parse_term(source)
    assert_true(word_literals(t).is_empty())
    let shown = word_render(source)
    assert_eq(shown.text, shown.canonical)
  }
}
