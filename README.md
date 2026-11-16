# CertiMoon

Proving MoonBit programs correct, down to the WebAssembly they compile
to. CertiMoon has WebAssembly's semantics and a separation logic for it,
in [hol_light.mbt](https://github.com/bobzhang/hol-light.mbt) (the
MoonBit port of HOL Light). The goal is to prove things about the wasm
binaries the MoonBit compiler emits, so that a proof does not trust the
compiler: only the HOL Light kernel and WebAssembly's definition.

- Package `wasm` is a port of
  [WasmCert-Isabelle](https://github.com/WasmCert/WasmCert-Isabelle)
  (BSD-2-Clause; see LICENSE and CONTRIBUTORS): the AST, the typing
  relations and the reduction relation `reduce`, with an evaluator checked
  against the official spec testsuite.
- Package `logic` is a program logic on top of it. Every rule is a theorem
  proved from `reduce`, so a proof trusts only the HOL Light kernel and
  the definition of WebAssembly. A triple means: from a state satisfying
  the precondition, the code does not trap, and if it ends, the
  postcondition holds (partial correctness, over every run).

What can be proved today: integer code, locals and globals, linear memory
(bytes, i32 and i64 words, arrays), `block`, `loop`, `if`, `br`, `br_if`,
`return`, and calls of the module's own functions, recursive ones too,
directly or through a function table (`call_indirect`). The examples
include a loop over an array, insertion sort, recursive factorial and a
recursive quicksort (see [The examples](#the-examples)). Not yet:
functions of other modules or the host, writing tables, floats, SIMD; and
there is no `.wat` or `.wasm` importer, so programs are written as terms. [PLAN.md](PLAN.md) has the design, what is next and how
to work on the code.

## Build and test

This module (`moonbit-community/certimoon`) needs hol_light's current
sources: it uses the term syntax, which the published `bobzhang/hol_light`
does not have yet. Its workspace (`moon.work`) resolves
`bobzhang/hol_light` to a hol-light.mbt checkout next to this one, so
clone the two side by side. The checkout is the `perf` branch of
[Yu-zh/hol-light.mbt](https://github.com/Yu-zh/hol-light.mbt/tree/perf):
upstream's `main` with the fixes this module needs that are not merged
yet, kept rebased on `main`. Without them the wasm and wasm-gc tests
overflow the stack while loading
([bobzhang/hol-light.mbt#1158](https://github.com/bobzhang/hol-light.mbt/pull/1158)).
This module was last tested with its commit `da8dc488`.

```bash
git clone -b perf https://github.com/Yu-zh/hol-light.mbt
git clone https://github.com/moonbit-community/certimoon
cd certimoon
```

A plain `moon check` here checks hol_light too and, like `moon info`,
rewrites its `pkg.generated.mbti` files. Check this module's packages
alone, which keeps their own interface files current:

```bash
moon check wasm logic tlsf
```

Do not run `moon fmt` here: it formats every workspace member, hol-light.mbt
included.

`moon test` in a workspace tests every member, hol_light included, so
select the package. The tests need a larger stack than the default. The
module's preferred target is wasm-gc, by far the fastest here:

```bash
ulimit -s 65520 && moon test -p moonbit-community/certimoon/wasm
```

```bash
ulimit -s 65520 && moon test -p moonbit-community/certimoon/logic
```

```bash
ulimit -s 65520 && moon test -p moonbit-community/certimoon/tlsf
```

Loading a package replays its proofs; there is no theorem cache. The
`logic` package contains the general program logic and examples. The
`tlsf` package loads that logic and then verifies the allocator. Loading
`logic` alone does not replay TLSF.

## Reviewing what is proved

Each package's tests keep its theory in two snapshots: `theory.md`, the
listing to read and diff, and `theory.json`, the same entries as data,
each with its statement, the constants it uses and defines, and the line
of the source that makes it. `tools/review_site.py` turns all three
`theory.json` files into a static site, published from `main` at
<https://moonbit-community.github.io/certimoon/> by
`.github/workflows/review-site.yml`. To build it locally:

```bash
python3 tools/review_site.py --out _site
```

Its front page shows the closed theorems (kind `theorem`: about a
program's runs, with no assertion or triple: `fact_closed`,
`apply_closed` and `quicksort_closed`) and what each depends on. It has a page per source file
(`wasm/reduction.html`, `logic/heap.html`, ...) with each entry's
statement, its constants linked to the entries that define them, what
uses it, and a link to its source; lemmas are folded, since the kernel
checks them. For each closed theorem and example, a page
(`review/fact_closed.html`, ...) shows its statement, then the code it
is about, then every other definition it depends on: what a reviewer
must read to trust it. Open
`_site/index.html` through a local server (`python3 -m http.server -d
_site`), since the pages load a stylesheet and a search index.

What a theorem depends on is computed by `@logic.depends_on`: the
entries defining the constants of its statement, and those defining the
constants of theirs, through `logic` and into `wasm`, until only
hol_light's constants are left. `logic/__snapshot__/dependencies.md`
and `tlsf/__snapshot__/dependencies.md` keep the lists for their respective
theorems and examples,
so a change to what a theorem trusts shows in a diff.

A closed theorem would hold trivially if nothing satisfied its
hypotheses together. Tests in `logic/logic_test.mbt` rule that out: for
each closed theorem, one builds a concrete store (with factorial's input
5, or quicksort's array [3, 1, 2] between other bytes), proves every
hypothesis about it in the kernel (the run by the evaluator, the rest by
computation), and so derives the conclusion for it; then it proves the
conclusion's first alternative for the run's result (120 on the stack;
the array sorted, the other bytes kept).

## Proving a program

### The pieces

**Code** is a list of WebAssembly instructions (`B_e`) written in
hol_light's term syntax, with WasmCert's constructor names:

```
[Local_get(0), Local_get(1), Binop(T_i32, Binop_i(Add)), Local_set(0)]
```

The constructors are in [wasm/ast.mbt](wasm/ast.mbt); `i32.const 4` is
`EConstNum(ConstInt32(word(4)))`, `i32.lt_u` is
`Relop(T_i32, Relop_i(Lt(U)))`, `i32.load` is `Load(T_i32, NONE, 2, 0)`
(alignment 2, offset 0), and a block is `Block(Tbv(NONE), [...])`.

**Assertions** describe a state by five things: the value stack `vs`, the
locals `lc`, the instance's globals `gs` (their values by index), the
memory's length in bytes `ms`, and the memory's bytes as a heap `h`. An
assertion is a term `(vs) (lc) (gs) (ms) (h) => ...` of type
`@logic.sassn`. Values are WasmCert's: the i32 x is `V_num(ConstInt32(x))`,
x a 32-bit word (`@logic.w32`; `val(x)` is its unsigned value).

The heap part uses separating conjunction: `star(p, q, h)` says h splits
into two disjoint heaps, one with p and one with q. `pts(a, bs)` is
exactly the bytes bs at address a, and `arr(a, xs)` the i32 words xs from
a. Every triple holds with any frame beside its heap, so the frame rule is
built in.

**Exact states** are what proofs usually start from:
`st(v, l, R)` says the stack is v, the locals l, and `R(gs, ms, h)`
(`R : @logic.rty`) holds of the rest, for example
`(gs) (ms) (h) => star(arr(val(p), xs), fp(gs, ms), h)`: the words xs at
p, and whatever `fp` says about the rest of memory and the globals.

**Triples**, each a theorem:

| Triple | For |
|---|---|
| `sl_triple(p, code, q)` | code without calls: for every store |
| `sl_triple_l(p, code, q, ls)` | the same with label assertions `ls` for `br` out of the code (innermost label first) |
| `sl_triple_m(fs, tabs, inst, p, code, q, ls)` | code in a module: stores whose functions are `fs` and tables `tabs`, run in instance `inst` |
| `sl_triple_g(G, fs, tabs, inst, rp, p, code, q, ls)` | code with calls and returns: `G` is a set of function specs the code may assume, `rp` the assertion a `return` must meet |

The theorem you want at the end is usually `sl_triple` (call-free code)
or `sl_triple_m` (a call into the module). What they claim is stated
with runs alone in `sl_triple_adequate` and `sl_triple_m_adequate`: from
a state with the precondition, every run (`reduce_trans`) reaches values
with the postcondition or a configuration that can step again, so no run
traps or gets stuck.

### A first proof

`sym_prove` proves a triple by running the code symbolically, from an
exact state, and leaves you the conditions it cannot close. In another
package, import `moonbit-community/certimoon/logic` (and the hol_light
packages for tactics, such as `bobzhang/hol_light/tactics`):

```moonbit
let w = @logic.w32
let i = (x : String) => "V_num(ConstInt32(\{x}))"
// local 0 becomes the larger (unsigned) of locals 0 and 1:
//   local.get 0; local.get 1; i32.lt_u; if; local.get 1; local.set 0; end
let code = "[Local_get(0), Local_get(1), Relop(T_i32, Relop_i(Lt(U))), If(Tbv(NONE), [Local_get(1), Local_set(0)], NIL)]"
let th = @logic.sym_prove(
  "api_max",
  "∀ vs0 : List[Value], ∀ x : \{w}, ∀ y : \{w}, ∀ R : \{@logic.rty}, sl_triple(st(vs0, [\{i("x")}, \{i("y")}], R), \{code}, st(vs0, [\{i("if word_ult(x, y) { y } else { x }")}, \{i("y")}], R))",
  [], // the loops' invariants: none
  [], // tactics for the conditions left: none
)
// th: ⊢ ∀ vs0 x y R. sl_triple(st(vs0, [x, y], R), code, st(vs0, [max, y], R))
```

This is a test in [logic/logic_test.mbt](logic/logic_test.mbt). sym_prove
went into both branches of the `if` (with `word_ult(x, y)` or its negation
as an assumption) and closed both endings by rewriting. `@logic.thm("api_max")`
reads the theorem back.

### Loops

A loop needs an invariant, `(lc) (gs) (ms) (h) => ∃ xs. lc == [...] &&
facts && ...`: the locals in terms of the variables xs, facts about them,
and the rest (memory, globals) as in an exact state. sym_prove proves the
invariant on entry, runs the body from it (the ∃s become variables, the
facts assumptions), and proves it again at each `br` back to the loop. It
leaves the conditions it cannot close: the invariant on entry and again,
the postcondition at the exit, and side conditions such as an address
being inside an array. Give a tactic for each in `vcs`, in order.

```moonbit
let inv = "(lc : List[Value]) => (gs : List[Value]) => (ms : Num) => (h : \{@logic.heap}) => ∃ n : \{w}, ∃ acc : \{w}, lc == [\{i("n")}, \{i("acc")}] && !(n == word(0)) && word_add(acc, word(sum_to(val(n)))) == word_add((acc0 : \{w}), word(sum_to(val((n0 : \{w}))))) && (R : \{@logic.rty})(gs, ms, h)"
```

is `example_sum`'s ([logic/example_sum.mbt](logic/example_sum.mbt)): its
proof is the code, this invariant and three one-line tactics. A `block`,
`if` or `loop` with more code after it also needs the state after it, in
`afters`. Arithmetic and list facts are best proved as lemmas first
(`@logic.lemma(name, statement, tactic)`) and used by the condition's
tactic (`@logic.by_lemma(th, [terms])` instantiates one at the
assumptions).

### Memory and arrays

Pass `rules=[...]` with the array rules to have sym_prove load and store:
`st_arr_load_at` and `st_arr_store_at` read and write the element at
`p + j * 4` of `arr(val(p), xs)` as `EL(val(j), xs)` and
`list_update(xs, val(j), x)`, leaving the side condition `val(p) + 4 *
LENGTH(xs) < 2^32 && val(j) < LENGTH(xs)`. The state's R must then be
`(gs) (ms) (h) => star(arr(val(p), xs), fp(gs, ms), h)`. See
`example_array_sum`, `example_insertion_sort` and the partition in
`example_quicksort`.

Words at unrelated addresses are cells: R is
`(gs) (ms) (h) => star(pts(val(a1), serialise_i32(x1)), star(..., fp(gs, ms)), h)`,
with the cells in any order. For an i32 `load` or `store`, sym_prove finds
the cell whose address is the instruction's (`val(k) + off == a` by
rewriting, with `rws`), brings it to the front and steps by
`st_cell_load` or `st_cell_store`. So write a cell's address as the code
computes it. Its ending compares states up to the order of the cells
when `rws` has `star_assoc`, `star_comm` and `star_left_comm`. A branch
whose test contradicts the statement's hypotheses (`c == word(0)` against
`!(c == word(0))`) is closed without running it, so a triple can be about
one path. See `tlsf_push_cons` and the other cases in tlsf/tlsf.mbt.

### Functions, calls and recursion

A module's functions are proved together, each from a spec:

1. Write the specs as a set `G`, a definition
   `G(inst, a, P, Q) == (a == sfunc_ind(inst, 0) && ∃ x. P == ... && Q == ...) || ...`:
   the function at address a takes arguments with P
   (`(args) (gs) (ms) (h) => args == [...] && ...`) and returns results
   with Q (`(res) (gs) (ms) (h) => ...`). Prove each spec as a theorem
   `∀ xs. G(inst, sfunc_ind(inst, j), P, Q)` (`fact_call`, `qs_call`).
2. Prove each body as `sl_triple_g(G(inst), fs, tabs, inst, post, pre, body,
   post, [post])` with `pre = @logic.body_pre(P, "args", zeros)` and `post
   = @logic.body_post(Q)`, by sym_prove with `specs=[...]`. A call uses a
   spec whose P is `args == [...] && R(gs, ms, h)`, matched against the
   stack. When a spec's variables cannot be read off the state (the parts
   of an array), give them for each call in `calls`: the call then leaves
   "P of its arguments" to prove. A body may call its own function. A
   `call_indirect` uses a spec the same way, for the function the table
   holds at the index on top of the stack, and leaves the table's facts
   to prove (`ti < LENGTH(inst_tabs(inst))`, `tab_cl_ind(tabs, EL(ti,
   inst_tabs(inst)), val(c)) == SOME(ConstRefFunc(a))` and the function's
   type), usually from the statement's hypotheses.
3. `sl_funs_g` turns the bodies' triples into the specs, for a store
   whose functions are these bodies (`fact_specs`, `quicksort_specs`).
4. A caller's triple: `sl_call_g` (the call), `sl_conseq_g`, and
   `sl_triple_m_of_g` to drop G and get an `sl_triple_m`.

[logic/example_fact.mbt](logic/example_fact.mbt) does this for factorial in
about 200 lines; [logic/example_qsort.mbt](logic/example_qsort.mbt) for two
functions that call each other; [logic/example_indirect.mbt](logic/example_indirect.mbt)
for a call through a function table.

### When a proof fails

- sym_prove's error lists the conditions it left, in order, and for each
  what its tactic left or why it failed.
- `@logic.set_trace(true)` makes `lemma` print each lemma's name and what
  its tactic leaves, and `@logic.show_goal("label")` inside a tactic print
  the goal there.
- Some names are HOL constants and cannot be variables: `T` and `F`
  (true and false), `I`, `K`, `S`, and constructors such as `U`
  (unsigned, from `Lt(U)`). A variable whose type
  nothing fixes gets a type variable and then matches nothing: write
  `(x : \{w})` in terms you build alone, such as an `exists_tac` witness.
- [PLAN.md](PLAN.md), "Things that will catch you out", has more, mostly
  about HOL Light's tactics.

### The API

Besides `@logic.load()`, `@logic.thm(name)` (any rule or lemma by name;
[logic/__snapshot__/theory.md](logic/__snapshot__/theory.md) lists them
all) and `@logic.listing()`:

| Function | Does |
|---|---|
| `sym_prove(name, stmt, invs, vcs, afters~, rules~, rws~, specs~, calls~)` | proves a triple by running its code |
| `lemma(name, stmt, tac)`, `def(name, eqs)`, `record(name, th)` | prove, define, record under a name for `thm` |
| `program(name, code)` | defines the constant `name` as `code` (a `List[B_e]`), and returns `name`, for statements to name the code; sym_prove and `call_free_tac` unfold it, and the listing shows it as WebAssembly text |
| `tm(s)`, `show(t)`, `ths(xs)` | parse and print terms, lists of theorems |
| `seq`, `solve`, `have(stmt, tac)`, `by_lemma(th, args)`, `forward2(th)` | putting tactics together |
| `subst_vars`, `subst_only(name)`, `split_conjs`, `use_eqs(pick)` | working on assumptions |
| `arith(stmt)` | a linear arithmetic fact |
| `args_of(t, name, n)`, `eq_of(t, prefix)`, `beta_goal()` | reading terms (for `use_eqs`), beta-reducing the goal |
| `call_free_tac` | proves `call_free_b(code)` for written-out code or a program's name |
| `w8`, `w32`, `w64`, `heap`, `hprop`, `assn`, `sassn`, `rty`, `fprop`, `specs_ty`, `sa_false` | the types and the false assertion, as term-syntax strings |
| `call_pre`, `call_post`, `body_pre`, `body_post` | the assertions of a call and of a function body, from a spec's P and Q |

Theorems a user proves after `load()` are recorded for `thm` but not added
to the package's theory listing.

## The examples

All in [logic/](logic), proved when the logic loads. Each names its code
with `program` (`sum_code`, `quicksort_code`, `partition_code`, ...), so
statements say which program they are about without writing it out; the
listing shows each program as WebAssembly text, printed from its
definition and read back to check it (`wasm/wat.mbt`).

| Example | File | Proves |
|---|---|---|
| `example_store_load` | examples.mbt | `i32.store` then `i32.load` gives the value back (rules glued by hand) |
| `example_sum` | example_sum.mbt | a loop on locals adds n0 + ... + 1 |
| `example_fill` | example_fill.mbt | a loop fills m words with x |
| `example_array_sum` | example_array_sum.mbt | a loop sums the words of an array |
| `example_insertion_sort` | example_sort.mbt | insertion sort: the words end sorted (unsigned) and a permutation |
| `example_call` | example_call.mbt | a call of a doubling function |
| `example_fact` | example_fact.mbt | recursive factorial, with an early `return` |
| `fact_closed` | example_fact.mbt | the same about runs (`reduce_trans`), with no assertion: every run of the call ends with the factorial or can step, and the locals, globals and memory are kept |
| `example_indirect` | example_indirect.mbt | `call_indirect`: whatever function table 0 holds at k, if it is the doubling function, the call doubles x |
| `apply_closed` | example_indirect.mbt | the same about runs, with no assertion: every run of `apply_code`, in a frame whose locals are x and k, ends with x + x or can step, and the store's functions and tables, the locals, globals and memory are kept |
| `example_quicksort` | example_qsort.mbt | recursive quicksort with a partition function: sorted, a permutation |
| `quicksort_closed` | example_qsort.mbt | the same about runs, with no assertion: the memory's bytes are `before ++ words_bytes(xs) ++ after`, and every run of the call ends with `before ++ words_bytes(ys) ++ after` for some sorted permutation ys of xs, or can step |

## MoonBit's allocator

The `moonbit-community/certimoon/tlsf` package owns the allocator proofs
and tests. Use `@tlsf.load()` to replay them and `@tlsf.thm("tlsf_free_all")`
to retrieve a theorem; general logic theorems remain available through
`@logic.thm`. Its listings are in
[tlsf/__snapshot__/theory.md](tlsf/__snapshot__/theory.md) and
[tlsf/__snapshot__/theory.json](tlsf/__snapshot__/theory.json).

[tlsf/tlsf.mbt](tlsf/tlsf.mbt) starts on MoonBit's TLSF allocator
(moonbitlang/malloc, which the compiler embeds for linear-memory wasm).
It defines the size classes as the compiled code computes them, with
`i32.clz`, and shifts that take the count modulo 32:

- `tlsf_fli(s) = 31 - clz(s)`, the first-level index;
- `tlsf_sli(s, f) = (s >> (f - 4)) & 15`, the second-level index;
- `tlsf_round(s)`, which rounds a request up to the next multiple of its class's width before `find` searches the bitmaps.

Then it proves three things:

| Lemma | Says |
|---|---|
| `tlsf_round_bounds` | for 16 ≤ s ≤ 0xF8000000 (`MAX_REQUEST_SIZE`), rounding doesn't wrap: s ≤ round(s) < s + 2^(fli(s) − 4), and round(s) is the least size of its class |
| `tlsf_find_sound` | every size in round(s)'s class, or in a class above it (what `find` searches), is at least s |
| `tlsf_class_mono` | a larger size is never in a lower class, so a free block of at least round(s) bytes is in a class `find` searches |

Then it verifies two of the allocator's functions, `Memory::push` and
`Memory::pop`, as the compiler embeds them: `tlsf_push_code` and
`tlsf_pop_code` are the compiled code instruction for instruction, with
`DATA_SECTION_END` as the constant d it is linked as.
`python3 tools/tlsf_wat_check.py PATH/TO/tlsf-mbt.wat` compares them with
the compiler's file (it needs `wasm-tools`). Each triple is about one path
through the code, from exactly the words that path reads and writes:

| Example | The path |
|---|---|
| `tlsf_push_cons`, `tlsf_push_nil` | push m into its bin, ahead of the bin's first memory nx (whose back link becomes m), or into an empty bin; the bin's bit and its level's bit are set |
| `tlsf_pop_mid`, `tlsf_pop_last` | pop m with a previous free memory pf: pf's next becomes m's next nf, and nf's back link (if nf isn't 0) pf |
| `tlsf_pop_head` | pop the first memory of a bin: the bin starts at nf, and nf's back link is 0 |
| `tlsf_pop_only` | pop a bin's only memory: the bin is empty, its bit is cleared, and the level's bit too if it was the level's last |

The bin's address comes from the code's own `27 - clz(size)`;
`tlsf_code_fli` and `tlsf_code_sli` say that is `tlsf_fli - 4` and the bin
`tlsf_sli`.

Then push and pop on a bin as a whole. `tlsf_bin(xs)` is a bin holding the
free memories xs: its head word is the first, or 0, and each memory's
links at m + 8 and m + 12 point to its neighbours in xs, or 0 at the ends
(`tlsf_dll`). The memories' link words belong to the bin, so the
separating conjunction makes them distinct.

| Example | Says |
|---|---|
| `tlsf_push` | from bin `xs`, with m's header and two link words beside it, push(m) leaves bin `m :: xs`, its head m, and the bin's and level's bits set |
| `tlsf_pop` | from bin `ys ++ [m] ++ zs`, pop(m) leaves bin `ys ++ zs` and m's two link words outside it, holding its old neighbours (`tlsf_prev(ys)`, `tlsf_hd(zs)`), and the bin's bit, and if that empties the level the level's bit, cleared exactly when `ys ++ zs` is empty |

Each is proved from the path triples (`tlsf_push_bin_cons`, ...,
`tlsf_pop_bin_mid`) by unfolding the list as far as that path reads it.
`tlsf_dll_append` splits a list at any member, for the pops in the middle
or at the end.

`tlsf_sync(s, n, ne)` says what a bitmap means: bit k of s is set exactly
when k < n and `ne(k)` (bin or level k is not empty). `tlsf_sync_set` and
`tlsf_sync_clear` say push's `|` and pop's `^` keep it, and `tlsf_sync_zero`
that the bitmap is 0 exactly when no bin is non-empty, which is what pop's
test for clearing the level's bit relies on. `tlsf_code_bounds`: for sizes
of at least 16 the code's bin is below 16 and its level below 28, so the
indices fit the bitmaps.

[tlsf/tlsf_bins.mbt](tlsf/tlsf_bins.mbt) combines all 448 bins and both
bitmap levels in `tlsf_bins(d, fl, sb, bl)`. Here `bl(f)(j)` is the list
in a bin, `sb(f)` its level's bitmap, and `fl` the first-level bitmap.
`tlsf_istar_focus` exposes one bin and frames out the other bins and
levels; `tlsf_sync_replace` describes keeping or clearing an occupied
entry's bit.

| Example | Says |
|---|---|
| `tlsf_push_all` | pushes m onto its size's bin, updates both bitmaps, and preserves the complete table invariant and the frame |
| `tlsf_pop_all` | removes m from any position in its size's bin, returns its two link words, and preserves the complete table invariant and the frame; clears the bin bit only when the bin becomes empty, and the level bit only when the level becomes empty |

[tlsf/tlsf_physical.mbt](tlsf/tlsf_physical.mbt) connects these bins to
the physical chain. The model is a list of addresses `xs` and a header
map `hd`: the size and the used/last flags at each address. The recursive
`tlsf_layout` places each next header immediately after the previous
block's payload, checks alignment and bounds, and ends at the memory's
length with `top` as the final block. `tlsf_coalesced` separately excludes
adjacent free blocks. Together with metadata placement and page-count
bounds these form `tlsf_physical_ok`, for an initialized allocator.

The memory length is a natural number: a full memory32 has length 2^32,
even though the allocator's byte-size word wraps to zero there.
`tlsf_block_field_address` proves that header/link field addresses do not
wrap; `tlsf_layout_order` and `tlsf_layout_distinct` establish that the
physical blocks do not overlap or repeat.

`tlsf_chain` owns the top pointer, both physical header words per block,
and the unused payload bytes of free blocks after their two link words.
The bin predicate owns those link words, and used payloads remain outside
these predicates. Thus `tlsf_large` separates the two sets of owned fields
and connects their models with `tlsf_bins_match`. That relation requires
each physical free block once in its size's bin and excludes used or
nonphysical blocks and entries in the wrong class. Occurrences are counted
within lists, so a duplicate in one bin is also excluded.

| Lemma | Says |
|---|---|
| `tlsf_bins_match_exact`, `tlsf_large_free_exact` | the count of m in any valid bin is 1 exactly when m is a physical free block of that class, and 0 otherwise |
| `tlsf_bins_match_unique` | if m occurs in two valid bins, they are the same bin and its occurrence count is 1 |
| `tlsf_large_free_once` | every physical free block has valid class indices and occurs exactly once in its class's bin |
| `tlsf_large_order` | the complete invariant implies non-overlap of physical blocks |

The compiler inlines its search into the first block of `Memory::take`.
The 136 instructions in `tlsf_find_code` include request alignment and
rounding, both bitmap searches, and both early returns. The transcription
checker compares that whole block, including branch depths, with the
compiler's WAT.

The search proof has two layers. `tlsf_find_query` establishes that the code
implements the bitmap model `tlsf_search` and preserves an arbitrary heap
assertion with a saved heap equality. `tlsf_find_all` applies that result to
`tlsf_large`: for requests from 16 through `MAX_REQUEST_SIZE` (4160749568),
the result is zero or the address of a physical free block whose payload
size is at least the request. The heap, memory length, combined invariant,
and client frame are preserved. This is the search block before the
allocator removes or splits the selected block.

The compiler also inlines `Memory::split` into `Memory::take`.
`tlsf_split_code(d, push)` contains the exact 112 instructions after pop:
the strict split guard, split, the real call to `Memory::push`, and the
final mark-used store. Marking the selected block used is needed to restore
coalescing: split alone temporarily leaves two adjacent free blocks.

`tlsf_split_whole`, `tlsf_split_last_all`, and `tlsf_split_next_all` prove module
triples for these three paths. Their entry is the state after pop: the
selected block is detached, the physical chain still describes it as free,
and the remaining bins match the model with that block marked used. The
postcondition restores `tlsf_large`, separates the allocated payload, and
preserves an arbitrary client frame and the memory length. A split inserts
the remainder exactly once in its correct class, transfers the last flag
and top pointer or repairs the successor's previous pointer, and leaves
the selected block used. The call proof uses the actual push code and its
native closure type.

The lower-level `tlsf_split_last` and `tlsf_split_next` preconditions expose
four arbitrary words in the selected free payload. `tlsf_split_payload_cut`
and `tlsf_bytes_four_words` justify this view of arbitrary bytes; those
new metadata words are allocator-owned. The `_all` specs hide these word
contents and start with ownership of the whole selected payload.
Existing used payloads remain in the unchanged client frame, which may
specify their exact saved bytes. The focused physical predicates fold back
with `tlsf_split_close`; the pure model update is `tlsf_split_focus` and
`tlsf_split_bins_focus`. Endpoints remain natural numbers through `2^32`.

`tlsf_take_code(d, pop, push)` is the complete 256-instruction
`Memory::take`, including both real helper calls and its successful
`return`. [tlsf_take_all](tlsf/tlsf_take_module.mbt) closes the composed proof against the actual
native take, pop, and push closures, with their declared local counts.
For requests from 16 through `MAX_REQUEST_SIZE`, failure returns zero
and preserves the exact heap. Success returns the selected free physical
block, marks it used, restores `tlsf_large`, and separates its payload of
at least the requested size from the arbitrary client frame.

`tlsf_pop_detach` connects the physical chain to the all-bins pop theorem;
`tlsf_split_detached` unifies the three split paths. Search preserves the
rounded size in local 3, and split preserves the selected address in
local 0, so the composition also proves the actual Wasm return. The
transcription checker compares the complete take body and checks all
three native signatures. These remain partial-correctness and non-trapping
specifications, as with the rest of the logic.

`tlsf_ensure_code(d, pop, push)` is the complete 156-instruction
`Memory::ensure`, with its real `memory.size`, `memory.grow`, pop, and
push instructions. [tlsf_ensure_all](tlsf/tlsf_ensure_module.mbt) closes
its proof against the actual native closures, including ensure's single
extra i32 local. For initialized heaps satisfying `tlsf_large` and requests
from 16 through `MAX_REQUEST_SIZE`, failure returns false with the exact
heap and memory length unchanged. Success returns true, restores
`tlsf_large`, and leaves the top free with capacity at least
`tlsf_round(tlsf_align(request))`. This includes both extending a free top
and appending a new top after a used block; every free block remains in
exactly one bin of the correct class.

Successful growth records the memory32 page limit and provides ownership
of the newly appended zero bytes. Existing client predicates remain
interpreted at the old memory length, so growth preserves the bytes the
client already owned. Endpoints include `2^32`, where `memory.size << 16`
wraps to zero but the computed block capacity is still correct. Zero-page
growth and unsigned underflow in the free-top page calculation are covered;
the contract does not require a preceding failed search. The checker
compares the complete ensure body and its native signature, and regression
tests cover page rounding, changed size classes, and growth to exactly 4 GiB.

`tlsf_free_code(d, pop, push)` is the complete 169-instruction
`Memory::free`. [tlsf_free_all](tlsf/tlsf_free_module.mbt) closes the
proof against the actual native free, pop, and push closures, including
free's two extra i32 locals. Its precondition requires a used physical
block and ownership of its entire payload, which the caller relinquishes.
The argument is the block's header address; its payload starts eight bytes
later.

The function clears the used flag, removes each free physical neighbor
from its bin, coalesces left and right, repairs the following previous
pointer or the stored top, and inserts the resulting block in its new
size class. The postcondition restores `tlsf_large`, so every free block
occurs exactly once in the correct bin and no adjacent blocks are free.
A free block covers the original allocation, every other live block
retains its address and size/flag word. Other client-owned bytes and the
memory length are preserved. The intermediate `tlsf_free_pending` predicate
accounts for the active block being absent from the bins while coalescing.
Regression tests execute interior coalescing and skipped-neighbor cases
with different bin orders and compare every byte. Model fixtures check
end coalescing, including the `2^32` endpoint. The WAT
checker compares the full body and native signature.

`tlsf_initialize_code(d, push)` is the complete 75-instruction
`initialize_memory`, with its real memory-size check, optional growth,
trap checks, header stores, native push call, and top-pointer store.
[tlsf_initialize_all](tlsf/tlsf_initialize_module.mbt) verifies its native
unit signature and three zero locals. Starting from a zeroed unused suffix
at the aligned static-data end, it establishes `tlsf_large` with one free
last block, listed exactly once in the correct class, and leaves the
small-page table zero. An arbitrary disjoint client assertion is preserved
at the original memory length, including when initialization grows memory.
The proof covers page boundaries and the memory32 endpoint.

The zero-suffix requirement is essential: this code relies on startup
zeroing instead of clearing the bin table or the physical previous pointer.
Memory growth may fail in WasmCert even within the declared limit; the
initializer then deliberately traps before writing allocator metadata.
The separate `sl_abort_m` rules prove that this outcome preserves the exact
old heap. Normal execution establishes the invariant; every reachable
configuration is normal, this specified abort, or can take another step.
The ordinary nontrapping triples retain their existing meaning. Runtime
regressions compare every byte on normal and out-of-memory paths, and the
WAT checker compares the complete initializer and native signature.

The small-page invariant is now defined by `tlsf_small` and connected to
`tlsf_large` by [tlsf_allocator](tlsf/tlsf_small_heap.mbt). Each page is a
used physical TLSF memory with at least 1080 bytes of capacity. Its size
is a multiple of eight between 8 and 256, and its slot count is
`1056 / (8 + size)`. Every slot occurs exactly once among the page-local
free list, global cached blocks, and live blocks. The header's `used`
count is cached plus live; it is zero exactly when both are empty.
Stable pages have positive `used`, and appear exactly once in the correct
partial-page list precisely when `used < total`. Both table heads and
all free-list links are owned by the invariant.

Live payloads remain entirely client-owned. In particular, the first
payload word is a free-list link only while free: the invariant places
no zero-word requirement on live payloads. Kernel proofs establish slot
bounds and separation, exact membership and accounting, the three model
transfers (cached to live, live to local, and exporting local slots),
and exclusion of pages from TLSF free bins. The ownership focus and
transport lemmas carry the small heap across TLSF calls that retain its
used backing blocks and capacities, including memory growth and changes
to last flags. `tlsf_allocator_client_write` proves that writes to
client-owned spans preserve the combined invariant. The initializer's
postcondition establishes it with no small pages and a zero table.
Nonempty model witnesses and rejection tests cover duplicates, missing
or foreign slots, wrong classes, incorrect partial lists, and invalid
backing memories. Optional execution tests use the sibling compiler WAT
to check the invariant and all live client bytes after mixed allocations
and frees, including cached slots that keep an otherwise empty page alive.

The complete compiled `Page::allocate` is verified by
[tlsf_page_allocate_all](tlsf/tlsf_page_allocate_module.mbt). Its native
closure has five locals and calls the actual compiled `take`, `pop`, and
`push` closures. A failed take returns zero with the exact old heap. A
successful call returns a new used backing memory of at least 1080 bytes,
preserves the combined invariant for existing pages, and initializes all
slots with tag 4, the owning page, and the reversed local free list.
`tlsf_page_allocate_slots_refine` connects the initialized prefix to the
ordinary small-slot and free-list heap predicates. The entire client frame
is preserved, including every byte of live payloads. The strengthened
`tlsf_retains` postcondition of take explicitly retains old used memories and their
size/flag words.

The result is an **unpublished page**: the shipped code does not write its
`used` or `prev` words. The proof preserves their arbitrary contents rather
than assuming they are zero. The caller must set `used` and publish the
slots before adding this page to the stable small-page model. Kernel
execution tests compare every byte for the initialization fragments and
full null-return path; optional tests execute complete pages from the
shipped WAT for all 32 size classes.
The WAT checker also compares all 99 instructions and the native signature.

The compiled inline `Block::free` branch is verified by
[tlsf_block_free_all](tlsf/tlsf_block_free_module.mbt). From the combined
invariant and a live slot with its payload ownership, it returns the slot
to its page, decrements `used`, and preserves the combined invariant and
an arbitrary disjoint client frame. A formerly full page enters its correct
partial list. Releasing the last counted slot unlinks the page at any list
position, recovers the entire backing payload, and invokes the verified
compiled TLSF free, including coalescing and bin updates. Cached slots
remain counted and prevent premature reclamation. The model removes only
the freed slot from the live set; all other client payloads remain framed.

The compiler inlines `Block::free` and `Page::free` in public `free`.
The theorem covers that exact 167-instruction small-block branch, checked
against the shipped WAT, with the actual Memory::free/pop/push closures.
The surrounding public guard, dispatch, and result drop are not yet
verified. Kernel execution tests cover release and all unlink paths;
shipped-WAT traces exercise full-page publication, every unlink position,
TLSF coalescing, and surviving small and large payload canaries.
Page publication on allocation and public malloc/free dispatch paths remain
to be verified.

## Reference: the program logic

The rules' statements are in
[logic/__snapshot__/theory.md](logic/__snapshot__/theory.md), in the order
they are proved, grouped by file. A snapshot test keeps it current
(`moon test --update` regenerates it). What follows is a map.

### Memory

Heaps are `(Num) -> Option[byte]`, with `hdisj`, `hunion`, `star`, `emp`,
points-to `pts(a, bs)`, and `heap_of(m)`, the heap a memory is
(`logic/heap.mbt`). `load_pts` and `store_pts` connect points-to with
WasmCert's `load` and `store` (`logic/memory.mbt`); `pts_split` splits a
points-to. `arr(a, xs)` is the i32 words xs from a (`logic/arrays.mbt`),
with `arr_split` and `arr_focus` (one element out of `ys ++ [x] ++ zs`).

### Triples

- `safe(n, s, f, es, q)`: for n steps, every run either has ended in values
  satisfying q or can step, and every step is safe for one step less; a
  trap is never safe, and every possible step counts (so memory.grow's
  choice is covered). `triple(p, bs, q)`: from a stack with p, bs is safe
  for every n. `sl_triple(p, bs, q)`: p and q as above, lifted to stores
  and frames with any frame r beside them on the instance's memory
  (`lift`, which also asks that the instance's global addresses are in the
  store and distinct, `globs_ok`). `logic/triple.mbt`.
- `safel` and `sl_triple_l` add label assertions: a run may stop at a `br`
  out of the code, if the label's assertion holds of its values
  (`logic/labels.mbt`). `sl_triple_l_of` carries every `sl_triple` over.
- `sl_triple_m(fs, tabs, inst, ...)`: `sl_triple_l` for the stores whose
  functions are fs and tables tabs, and the frames of instance inst
  (`keep`); every triple of call-free code is one (`sl_triple_m_of`, from
  `call_free_step`: a step of call-free code, with no call and no table
  write, keeps the functions, the tables and the instance).
  `logic/calls.mbt`.
- `safer` adds a return assertion: a run may stop at a `return` whose
  values meet it (`logic/returns.mbt`). `sl_triple_g(G, fs, tabs, inst, rp,
  ...)` holds for n steps whenever the function specs G do (`specs_ok(n, G,
  fs, tabs, inst)`: calling each is safe for n steps or fewer), which is what lets a
  body assume its own spec (`logic/specs.mbt`). `sl_triple_g_of` brings in
  any triple of call-free code, `sl_triple_m_of_g` drops G.
- Adequacy (`logic/adequacy.mbt`): `safe_adequate` says what safety for
  every n means for a run (`reduce_trans`): its end is values with q, or
  can step. `sl_triple_adequate` and `sl_triple_m_adequate` (no labels)
  say it of a triple's code from a state with the precondition, lifted
  with a frame r, so they can be read instead of `safe`, `safel`,
  `triple_l` and `keep`. `sl_triple_m_adequate_whole` has no frame (r is
  `emp`, `star_emp_r`): the precondition holds of the instance's whole
  memory j, and no heap assertion is left; `fact_closed` comes from it.
  `arr_in_mem` says an array with the bytes before and after it is the
  memory's list of bytes, `before ++ words_bytes(ys) ++ after`, so
  `quicksort_closed` states the memory with lists alone.

### Instruction rules

`logic/rules.mbt`, `globals.mbt`, `locals.mbt`, `memsize.mbt`,
`arrays.mbt`, `conditionals.mbt`. Each instruction's operands sit on top of
a stack of any length:

- `sl_const`, `sl_unop`, `sl_binop`, `sl_testop`, `sl_relop`, `sl_convert`,
  `sl_reinterpret`, `sl_nop`, `sl_drop`, `sl_select`: the value computed
  by WasmCert's `app_binop` and the others;
- `sl_load_i32`, `sl_store_i32`, `sl_load_i64`, `sl_store_i64`, and the
  packed ones (`sl_load_packed_i32` and others): against `pts(val(k) + off,
  bs)`, bs of the access's length;
- `sl_memory_size`, `sl_memory_grow` (which may always fail, pushing -1);
- `sl_global_get`, `sl_global_set`, `sl_local_get`, `sl_local_set`,
  `sl_local_tee`;
- the structural rules: `sl_conseq`, `sl_frame`, `sl_seq` (and their `_l`,
  `_m` and `_g` versions), `sl_ex_l`, `sl_pure_l`, `sl_nil_l`.

Each rule's proof follows one pattern (`arity_`, `prefix_`, `step_cases`;
PLAN.md, "Adding an instruction rule").

### Control flow

`logic/labels.mbt`, `block.mbt`, `loop.mbt`, `conditionals.mbt`, and their
`_g` versions in `specs.mbt`:

- `sl_br`: `br i` with the i-th label assertion of its values;
- `sl_block` (block types `Tbv(ot)`, no parameters): the body with label 0
  assertion lb (of the block's arity); the block leaves `vs0 ++ r`, the
  body's postcondition or lb of r;
- `sl_loop`: an invariant that holds on entry and at each `br 0`;
- `sl_br_if`, `sl_if`: with an i32 c on the stack, the case it steps to;
- `sl_return_g`: `return` with the return assertion of its values.

### Exact states and symbolic execution

`logic/state.mbt` has the rules on exact states (`st_const`, `st_binop`,
`st_unop`, `st_local_get`, `st_local_tee`, `st_drop`, ..., and in
arrays.mbt `st_arr_load_at` and the cell rules `st_cell_load` and
`st_cell_store`): each steps from one written-out state to the next,
computed by `norm`. `logic/sym.mbt` has sym_prove: it
takes the code's first instruction, applies its `st_` rule (or goes into a
block, loop or if), and leaves entailments for the ends of the code, the
`br`s and the side conditions. Its rules are `sl_step_l`, `sl_cons_l`,
`sl_if_st`, `sl_br_if_st`, `sl_block_st`, `sl_loop_st`, `sl_br_st`,
`sl_nil_st`, `sl_pre_l`, and for g triples their `_g` versions with
`sl_call_st_g`, `sl_call_spec_g`, `sl_call_indirect_st_g` and
`sl_return_st_g`.

### Calls

`logic/frames.mbt`, `call_rule.mbt`, `specs.mbt`: frames behave like labels
(`frame_steps`, `frame_safe`, `frame_safe_r` with returns); a return waiting
in contexts does not step by itself (`return_stuck`); `call j` steps to
`Invoke(sfunc_ind(inst, j))`, which becomes the function's frame
`Frame(m, Wframe(args ++ zeros, inst), [Label(m, NIL, body)])`
(`call_step`, `invoke_step`). `sl_call` is a call of a function given its
body's triple (no recursion); `sl_call_g` a call by a spec of G, and
`sl_funs_g` proves G's specs from their bodies. `logic/indirect.mbt`:
`call_indirect(ti, j)` with c on the stack, when table ti holds the
function a at c and a has type j, steps only to `Invoke(a)`
(`call_indirect_step`); `sl_call_indirect_g` is then a call of a by its
spec in G.

## Reference: the semantics (package wasm)

Package `wasm` has the definitions of Wasm_Ast, Wasm_Type_Abs/Word,
Wasm_Base_Defs, Wasm_Subtyping and Wasm.thy: the WebAssembly AST, the
numeric layer (on Library/words), and the typing and reduction relations.
The header comments of `wasm/*.mbt` list where names and representations
differ from Isabelle's. The soundness proofs (Wasm_Properties,
Wasm_Soundness) are not ported. Its theory is listed in
[wasm/__snapshot__/theory.md](wasm/__snapshot__/theory.md).

```moonbit
@wasm.load()
let rules = @wasm.thm("reduce_rules") // also b_e_typing_rules, typeof_num, ...
```

### Running programs

`run` executes a configuration `(s, f, es)` and proves each step from the
reduction rules; `outcome` states the result as `computes` (the run ends in
values) or `traps`. Programs are written with the builder (`Instr`,
`Value`, `config`), which makes the HOL terms through the kernel:

```moonbit
let cfg = @wasm.config([
  I32Const(10), I32Const(2), Binop(I32, Div(Signed)),
])
let th = @wasm.outcome(cfg)
// th: ⊢ computes(cfg, s, [V_num(ConstInt32(word(5)))])
@basics.aconv(@kernel.concl(th), @wasm.computes_stmt(cfg, [I32Val(5)])) // true
```

`config` runs the instructions in any store `s` and instance `i` (it
takes `locals~`, and `store~`/`inst~` to fix them), so the theorem holds
for all of them. `computes_stmt` and `traps_stmt` state an expected
result to compare with. `compute_conv(defs)` is the conversion the
evaluator decides side conditions with (rewriting with the port's
definitions and `defs`, and word and numeral arithmetic), for proving
facts about a written-out store; the closed theorems' non-vacuity checks
in `logic/logic_test.mbt` prove their hypotheses with it.

The evaluator covers integer instructions (const, unary, binary, `eqz`,
comparisons, `i32.wrap_i64`, `i64.extend_i32_s/u`, `extend8_s` and the
other sign extensions), `ref.null`,
`ref.is_null`, `unreachable`, `nop`, `drop`, `select`, `block`, `loop`,
`if`, `br`, `br_if`, `br_table`, `local.get/set/tee`, `global.get/set`,
`call` (of native functions), `call_indirect` and `return`, loads and
stores (packed too), `memory.size`, `memory.grow`, `memory.fill`,
`memory.copy`, and traps; these are the builder's instructions (`store`
takes `tables` of function indices for `call_indirect`). Floating
point (left unspecified, as in Isabelle), host functions, vector
instructions and the table instructions (`table.get`, `table.set`, ...)
are not covered: a term written out with them
raises "no rule for". `run` also takes a term built any other way, when
its instruction list, frame and (for globals, memory and calls) store are
written out. A `computes` theorem is about one run: the port does not
prove that reduction is deterministic, so it does not yet rule out a
trapping run, and `memory.grow` may fail in any state (the evaluator takes
the step that grows when it can). `wasm/eval_test.mbt` has examples.

`store` writes out a store and its instance: functions (`Func`: parameter,
result and local types, and a body), the types of blocks with several
results or with parameters (`types~`, for `TypeIndex`), a memory and
mutable globals.

```moonbit
let st = @wasm.store(memory=[b'\x01', b'\x02', b'\x03', b'\x04'])
let cfg = @wasm.config([I32Const(0), Load(I32, 0)], store=st.0, inst=st.1)
let th = @wasm.outcome(cfg) // ⊢ computes(cfg, s, [V_num(ConstInt32(word(67305985)))])
```

Memory is a byte list and loads and stores compute on it byte by byte, so
the evaluator suits small memories; `store` does not round them to pages.

`wasm/spec_test.mbt` checks the evaluator against the WebAssembly spec
testsuite: the 758 integer assertions of `i32.wast` and `i64.wast`, the 60
integer loads of `address.wast` at address 0 (in a memory of its data and
zeros: the other addresses test the end of a 64 KiB page), and 543
integer assertions of `block.wast`, `loop.wast`, `br.wast`, `br_if.wast`,
`br_table.wast`, `call.wast`, `return.wast` and `call_indirect.wast`,
which test the reduction rules of control flow, labels, frames and calls,
direct and through tables. Each holds as a theorem.

For the control-flow files, `tools/spec_cases.py` translates each module's
functions to `Func`s and its tables to the tables its element segments
leave, and a case calls an exported function in a store of them; a
module's assertions run in order, each in the memory and globals the one
before left. What the script does not translate (floats, references and
the table instructions, `memory.size` and `grow`) is left out, and so is
`assert_exhaustion`; the generated file counts what each file leaves out.
Sixteen deep recursions of `call.wast` and `call_indirect.wast` (`fac
25`, `fib 20`, `even 100`, ...: `SLOW` in the script) take minutes to
hours to prove step by step, so only a skipped test runs them:

```bash
ulimit -s 65520 && moon test -p moonbit-community/certimoon/wasm --target wasm-gc --release --include-skipped -f '*slow ones too*'
```
`tools/spec_cases.py` writes `wasm/spec_cases_test.mbt` from the
testsuite files; the header of that file names the testsuite commit and
the command.

### Facts about reduction

`wasm/props.mbt` proves the facts a program logic needs about `reduce`
(on first use, or with `@wasm.props()`; read them with `@wasm.thm`):

- `reduce_not_vals`, `reduce_not_trap`: values and `[Trap]` do not step.
- `lfilled_eq`: an evaluation context is a function,
  `Lfilled(k, lh, es, les) ⇔ k = lh_depth(lh) ∧ les = lfill(lh, es)`; so
  `lfilled_deterministic`, and contexts compose (`lfill_compose`).
- `reduce_decompose`: a step is a base step (`reduce_base`: every rule but
  the context rule) inside a context.
- `reduce_append`: a step of `es1 ++ es2`, `es1` not all values, is a step
  of `es1` with `es2` kept, unless `es1` has a trap at the top
  (`trap_top`).
- `step_basic`: a step of values then one instruction is a base step of
  that instruction with some of the values before it.

`@wasm.step_cases(s, f, es)`, for `es` values then one basic instruction,
proves what it can step to: `∀ s' f' es'. reduce(s, f, es, s', f', es') →
D`, with the side conditions of each case computed as far as they go (for
`10 / 2`, `s' = s ∧ f' = f ∧ es' = [5]`). The tests check, for each
instruction the evaluator covers, that its step is the only one.
