# Generic HOL rendering

Package `moonbit-community/certimoon/render` renders HOL terms and theory
listings without importing the Wasm semantics or the separation logic.
It owns statement layout, local notation rules, constant discovery, dependency
closure, Markdown listings, and JSON export. Clients supply type abbreviations
and specialized displays; Wasm keeps its word aliases and WAT printer.

With no notation rules, `layout_statement` preserves the existing layout.
The compatibility helpers in `wasm` keep their original defaults.

## Local infix notation

After the client has defined `star`, it can render it with:

```moonbit
let star = @kernel.mk_const("star", @list.List([]))
let infix = @render.Infix::new(
  star,
  symbol="*",
  precedence=60,
  associativity=Right,
)
let shown = @render.statement(conclusion, infixes=[infix])
```

`Infix::new` takes a typed HOL constant with at least two arguments. Rules
match that exact constant and type, so variables with the same name and other
type instances are unaffected. Pass another rule for another type instance.
Rules are passed explicitly and never alter HOL's parser or overload tables.

Larger precedence binds more tightly (values 1 through 999). Associativity
is `Left`, `Right`, or `NonAssociative`; it controls omitted parentheses and
never reassociates the term. With a right-associative rule:

```text
star(P, star(Q, R))  => P * Q * R
star(star(P, Q), R)  => (P * Q) * R
star(P, Q, h)        => (P * Q)(h)
star(P)             => star(P)
```

Built-in syntax is parenthesized conservatively when used as an infix operand.
Operands retain their expected result type while printing, so polymorphic
literals such as `word(15)` need no repeated constructor type annotations.
Other syntax and binders use the existing HOL term printer. Its temporary
slots are restored structurally and checked against the original term;
unsupported custom printing falls back to the original checked layout.

`statement` returns `text`, `canonical` (the original layout), and `references`
for notation symbols. Reference offsets count Unicode scalar values.
Pass `references` and `canonical` to `export_entry` to preserve definition
links and an Original statement disclosure in the review site. The canonical
layout, with its existing type abbreviations, remains the review text;
custom symbols are display notation and are not fed to the proof parser.

For a complete literal term, pass an atomic rule alongside any infix rules:

```moonbit
let literal = @render.Atom::new(exact_term, text="32w")
let shown = @render.statement(conclusion, atoms=[literal], infixes=[infix])
```

An `Atom` matches an exact closed term and type, headed by a constant. Its
display is a single token; its reference identifies the head constant.
`Statement::join(parts, separator="\n\n")` combines separately rendered
pieces while preserving their canonical layouts and Unicode reference offsets.
Match syntax can rename its internal pattern binders when all substituted
terms are closed; the restored term is still checked against the original.

Logic and TLSF listings configure `star` as `*`. Numeric multiplication keeps
its own identity and does not acquire a link to `star`.

The Wasm client supplies additional rules through `@wasm.word_infixes(term)`.
The rule table lives in `wasm/notation.mbt`; each rule is instantiated at the
word types occurring in the term. Logic and TLSF include these rules in their
listing profile. For 32-bit words:

| HOL constant | Display |
|---|---|
| `word_add` | `+₃₂` |
| `word_sub` | `−₃₂` |
| `word_mul` | `×₃₂` |
| `word_and` | `&₃₂` |
| `word_xor` | `^₃₂` |
| `word_or` | `\|₃₂` |
| `word_jshl` | `<<₃₂` |
| `word_jshr` | `>>₃₂` (signed) |
| `word_jushr` | `>>>₃₂` (unsigned) |

Arithmetic wraps at the indicated width. Shift counts are taken modulo that
width. Other fixed widths use their own subscripts, and an arbitrary word
width uses `ʷ`. These are display rules; they retain the original constants,
grouping, and canonical statements. The generic renderer and the Python site
generator require no additional operator cases.

`@wasm.word_literals(term)` supplies atomic rules for word literals:
`word(32)` becomes `32w`, including when no infix rule applies. Only numeral
arguments receive the suffix. Computed conversions such as `word(n)`,
`word(16 + 16)`, and `word(word_clz(hd))` remain explicit. The numeral keeps
its original value, including values larger than the word width, and the
width remains in types and operator subscripts. Wasm, logic, and TLSF listings
include these rules; their Original statement disclosures retain HOL syntax.

## Other theories

The site generator also accepts arbitrary exported HOL theories:

```sh
python3 tools/review_site.py --root . --out _site \
  --theory algebra/__snapshot__/theory.json \
  --theory order/__snapshot__/theory.json --title 'Algebra review'
```

Each JSON input names its package in `package`. With no `--theory` arguments,
the existing Wasm, logic, and TLSF inputs and site text are preserved.

Run the standalone renderer and site tests with:

```sh
moon test render --target native
python3 -m unittest discover -s tools -p review_site_test.py
```
