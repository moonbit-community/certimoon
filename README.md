# wasmcert

A port of [WasmCert-Isabelle](https://github.com/WasmCert/WasmCert-Isabelle)
(BSD-2-Clause; see LICENSE and CONTRIBUTORS) to [hol_light.mbt](https://github.com/bobzhang/hol-light.mbt),
the MoonBit port of HOL Light.

## Build

This module (`moonbit-community/wasmcert`) needs hol_light's current
sources: it uses the term syntax, which the published `bobzhang/hol_light`
does not have yet. Its workspace (`moon.work`) resolves
`bobzhang/hol_light` to a hol-light.mbt checkout next to this one, so
clone the two side by side:

```bash
git clone https://github.com/bobzhang/hol-light.mbt
git clone https://github.com/moonbit-community/wasmcert
cd wasmcert
```

A plain `moon check` here checks hol_light too and, like `moon info`,
rewrites its `pkg.generated.mbti` files. Check this module's packages
alone, which keeps their own interface files current:

```bash
moon check wasm logic
```

## Status

Package `wasm` has the definitions of Wasm_Ast, Wasm_Type_Abs/Word,
Wasm_Base_Defs, Wasm_Subtyping and Wasm.thy: the WebAssembly AST, the
numeric layer (on Library/words), and the typing and reduction relations.
The header comments of `wasm/*.mbt` list where names and representations
differ from Isabelle's. The soundness proofs (Wasm_Properties,
Wasm_Soundness) are not ported yet.

Package `logic` is a separation logic for linear memory on top of it, with
rules for constants, binary operators, comparisons, `i32.load`, `i32.store`,
locals, globals, `br`, `br_if`, blocks, `if` and loops, and arrays of i32
words. See "Program logic" below, and [PLAN.md](PLAN.md) for the design,
what is left and how to work on it.

```moonbit
@wasm.load()
let rules = @wasm.thm("reduce_rules") // also b_e_typing_rules, typeof_num, ...
```

## What is defined and proved

Each package writes its theory as a document: every definition, datatype,
relation (one rule per line) and lemma, in order, with the kernel's
statement of it and short names for the long types:

- [wasm/__snapshot__/theory.md](wasm/__snapshot__/theory.md): the WebAssembly
  semantics and the facts about reduction;
- [logic/__snapshot__/theory.md](logic/__snapshot__/theory.md): the program
  logic, its rules and examples.

They are snapshot tests (`wasm/theory_test.mbt`, and one in `logic/logic_test.mbt`): a test fails when the file no
longer matches what the package proves, and `moon test --update`
regenerates it. Statements only: the proofs are the tactic code in the
`.mbt` files, and loading a package checks them all.

## Running programs

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
result to compare with.

The evaluator covers integer instructions (const, unary, binary, `eqz`,
comparisons, `i32.wrap_i64`, `i64.extend_i32_s/u`), `ref.null`,
`ref.is_null`, `unreachable`, `nop`, `drop`, `select`, `block`, `loop`,
`if`, `br`, `br_if`, `br_table`, `local.get/set/tee`, `global.get/set`,
`call` (of native functions) and `return`, loads and stores (packed
too), `memory.size`, `memory.grow`, `memory.fill`, `memory.copy`, and
traps; these are the builder's instructions. Floating point (left
unspecified, as in Isabelle), indirect calls, host functions, vector
instructions and tables are not covered: a term written out with them
raises "no rule for". `run` also takes a term built any other way, when
its instruction list, frame and (for globals, memory and calls) store are
written out. A `computes` theorem is about one run: the port does not
prove that reduction is deterministic, so it does not yet rule out a
trapping run, and `memory.grow` may fail in any state (the evaluator takes
the step that grows when it can). `wasm/eval_test.mbt` has examples.

`store` writes out a store and its instance: functions (`Func`: parameter,
result and local types, and a body), a memory and mutable globals.

```moonbit
let st = @wasm.store(memory=[b'\x01', b'\x02', b'\x03', b'\x04'])
let cfg = @wasm.config([I32Const(0), Load(I32, 0)], store=st.0, inst=st.1)
let th = @wasm.outcome(cfg) // ⊢ computes(cfg, s, [V_num(ConstInt32(word(67305985)))])
```

Memory is a byte list and loads and stores compute on it byte by byte, so
the evaluator suits small memories; `store` does not round them to pages.

`wasm/spec_test.mbt` checks the evaluator against the WebAssembly spec
testsuite: the 720 integer assertions of `i32.wast` and `i64.wast` (all
but the `extend*_s` operators, which the builder lacks), and the 60
integer loads of `address.wast` at address 0 (in a memory of its data and
zeros: the other addresses test the end of a 64 KiB page). Each holds as a
theorem. `tools/spec_cases.py` writes `wasm/spec_cases_test.mbt` from the
testsuite files; the header of that file names the testsuite commit.

## Facts about reduction

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

## Program logic

Package `logic` is a separation logic for linear memory, proved from the
port's definitions (no axioms; `@logic.load()`, then `@logic.thm`):

- heaps (`(Num) -> Option[byte]`), `hdisj`, `hunion`, `star`, `emp`,
  points-to `pts(a, bs)`, and `heap_of(m)`, the heap a memory is;
- `star_comm`, `star_assoc`, `star_mono`;
- `read_pts`: if `heap_of(m)` satisfies `star(pts(a, bs), r)` (bs not
  empty), the bytes are inside m and `read_bytes(m, a, LENGTH(bs)) = bs`;
- `write_pts`: writing bs2 (as long as bs) there gives
  `star(pts(a, bs2), r)`: the frame r still holds;
- `load_pts`, `store_pts`: the same for WasmCert's `load` and `store` at
  `n + off`, the functions the load and store reduction rules use;
- `pts_split`: `pts(a, xs ++ ys)` is `star(pts(a, xs), pts(a + LENGTH(xs), ys))`.

Triples are defined over the reduction relation:

- `safe(n, s, f, es, q)`: for n steps, every run either has ended in
  values satisfying q or can step, and every step is safe for one step
  less; a trap is never safe, and every possible step counts (so
  memory.grow's choice is covered);
- `triple(p, bs, q)`: from a value stack satisfying p, the instructions bs
  are safe for every n (partial correctness, no traps);
- `sl_triple(p, bs, q)`: p and q are heap assertions on the value stack,
  the locals, the globals (`gvals(s, f)`: the instance's globals by index)
  and the memory's length in bytes, and the triple holds with any frame
  beside them on the instance's memory (`lift`). `lift` also asks that the instance's global
  addresses are in the store and distinct (`globs_ok`).

Rules, all theorems:

- `sl_conseq`, `sl_frame` (from `star_assoc`), `sl_const`;
- `sl_binop`: a binary operator whose `app_binop` is `SOME(c)` replaces its
  two operands by c;
- `sl_load_i32`: with `pts(val(k) + off, bs) * p` (bs 4 bytes), `i32.load`
  replaces the address k by `deserialise_i32(bs)`;
- `sl_store_i32`: it turns `pts(val(k) + off, bs)` into
  `pts(val(k) + off, serialise_i32(v))` and pops k and v;
- `sl_load_i64`, `sl_store_i64`: the same with 8 bytes and
  `deserialise_i64`, `serialise_i64` (the address is still an i32);
- `sl_load_packed_i32`, `sl_load_packed_i64`: for any packing tp
  (`Tp_i8`, `Tp_i16`, `Tp_i32`) and extension sx (`U`, `S`), with bs of
  `tp_num_length(tp)` bytes, `i32.load8_u` and the others push
  `deserialise_i32(sign_extend(sx, 4, bs))` (8 for i64);
- `sl_store_packed_i32`, `sl_store_packed_i64`: `i32.store8` and the others
  write the value's low bytes,
  `bytes_takefill(zero_byte, tp_num_length(tp), serialise_i32(v))`, over
  `tp_num_length(tp)` owned bytes (from `store_pts_fill`);
- `sl_unop` (`app_unop`), `sl_nop` (`sl_triple(p, [Nop], p)`), `sl_drop`
  and `sl_select` (of any values, numbers, vectors or references: `select`
  keeps v1 if the i32 b is not 0, else v2);
- `sl_convert`: for c of type t1 (`typeof_num(c) == t1`) and
  `cvt(t2, sat_sx, c) == SOME(d)`, `Cvtop(t2, Convert, t1, sat_sx)`
  (`i32.wrap_i64`, `i64.extend_i32_u`, ...) replaces c by d;
- `sl_reinterpret`: for c of type t1, `Cvtop(t2, Reinterpret, t1, NONE)`
  replaces c by `wasm_reinterpret(t2, c)`;
- `sl_memory_size`: pushes the length in pages, `DIV(ms, 65536)`;
- `sl_memory_grow` by c pages: either it pushes the old size in pages, the
  length grows by `c * 65536` and `pts(old length, zeros)` appears beside
  the precondition (`star_grow`), or (it may always) it pushes -1 and
  nothing changes;
- `sl_global_get`: `global.get i` (i < LENGTH(gs)) pushes `EL(i, gs)`;
- `sl_global_set`: `global.set i` pops a number c, and the globals become
  `list_update(gs0, i, c)` of the globals gs0 before (`gvals_set`, which
  needs the addresses distinct);
- `sl_local_get`, `sl_local_set`: the same for the locals (`local.get k`
  pushes `EL(k, ls)`), from `local_get_cases` and `local_set_cases`, which
  state their steps for any frame (the reduction rules take the locals
  split at k: `split_at`);
- `sl_local_tee`: `local.tee k` keeps c on the stack and sets local k; it
  steps to `[c, c, local.set k]`, so the rule comes from `sl_const` and
  `sl_local_set`.

Each rule's operands sit on top of a stack of any length. `prefix_<op>`
shows that a step of such a configuration is a step of the instruction and
its operands alone: `arity_<op>` says the instruction's base step takes
exactly its operands (from the cases of reduce_base), and `step_cases`
(with `compute=false` for the store) says what that step is.

Sequencing: `safe_seq` (by induction on n: a step of `APPEND(es1, es2)`
is a step of es1 by `reduce_append`, and a trap at the top of es1 leaves
only `[Trap]`, which is never safe for a step more), then `triple_seq` and
`sl_seq`: `sl_triple(p, bs1, q)` and `sl_triple(q, bs2, r)` give
`sl_triple(p, APPEND(bs1, bs2), r)`.

`logic/examples.mbt` verifies a program with the rules alone, gluing rule
instances with `sl_seq` and `sl_conseq`: `example_store_load` says that
`[i32.const k; i32.const v; i32.store; i32.const k; i32.load]`, from
`pts(val(k) + off, bs) * p` (bs 4 bytes), ends with v on the stack and
`pts(val(k) + off, serialise_i32(v)) * p` (`deserialise_serialise_i32`:
loading back what was stored gives the value). The other examples are
proved by symbolic execution (below). `example_sum` verifies a loop on
locals: from locals `[n0, acc0]`,

```
local.get 0
if
  loop
    local.get 1; local.get 0; i32.add; local.set 1
    local.get 0; i32.const 1; i32.sub; local.set 0
    local.get 0; br_if 0
  end
end
```

ends with locals `[0, acc0 + sum_to(val(n0))]` (`sum_to(n)` is
1 + ... + n; the additions are on words), and the stack and `R` (the
globals and memory) as they were. The rules on exact states
(`logic/state.mbt`) are what the symbolic execution runs: `st(v, l, R)`
says the stack is v, the locals l and R holds of the globals and heap, and
the `st_` rules (from the rules above) step from one exact state to the
next, written out by `norm`.

Arrays (`logic/arrays.mbt`): `arr(a, xs)` is the i32 words xs from address
a (`pts` of their bytes, `words_bytes`). `arr_split` splits an array into
two, and `arr_focus` takes one element out of `ys ++ [x] ++ zs`, at
`a + 4 * LENGTH(ys)`. The rules `st_arr_store` and `st_arr_load` are
`i32.store` and `i32.load` of that element, on exact states whose `R` is
`star(arr(a, ...), fp(gs))`. `example_fill` (`logic/example_fill.mbt`)
verifies a loop over memory with them:

```
local.get 1
if
  loop
    local.get 0; i32.const x; i32.store
    local.get 0; i32.const 4; i32.add; local.set 0
    local.get 1; i32.const 1; i32.sub; local.set 1
    local.get 1; br_if 0
  end
end
```

from locals `[p0, m]` and m words at `val(p0)` (if `val(p0) + 4m < 2^32`)
ends with locals `[p0 + 4m, 0]` and the words `REPLICATE(val(m), x)`. Its
invariant keeps the array as the copies of x written so far, then the
words still to write; `fill_step` and `fill_exit` are the arithmetic and
list facts that keep it.

`sl_testop` and `sl_relop` (and `st_testop`, `st_relop`) are the rules for
`i32.eqz` and the comparisons: they push `app_testop(op, c)` or
`app_relop(op, c1, c2)`, which `norm` computes to `wasm_bool(...)` of the
word comparison. `example_array_sum` (`logic/example_array_sum.mbt`) reads
an array in a loop whose condition is `i32.lt_u`: from locals
`[p, n, 0, 0]` and the n words xs at `val(p)` (if `val(p) + 4n < 2^32`),

```
local.get 2; local.get 1; i32.lt_u
if
  loop
    local.get 3
    local.get 0; local.get 2; i32.const 4; i32.mul; i32.add
    i32.load
    i32.add; local.set 3
    local.get 2; i32.const 1; i32.add; local.set 2
    local.get 2; local.get 1; i32.lt_u; br_if 0
  end
end
```

ends with locals `[p, n, n, wsum(xs)]` (the words' sum) and the array
unchanged.

Symbolic execution (`logic/sym.mbt`): `sym_prove(name, stmt, invs, vcs)`
proves a triple `sl_triple(st(...), code, q)` (after hypotheses) given an
invariant for each loop, `λ lc gs ms h. ∃ xs. lc == l && facts && ...`.
`sym_tac` runs the code: each straight-line instruction by the `st_` rule
that matches the state (with `app_binop` and the others computed),
`br_if` and `if` by going into both cases with the condition as an
assumption, `block` and `loop` by going into the body (the loop's
precondition taken apart into variables, facts and an exact state), and
`br` and the end of the code by an entailment. The rules it uses are
`sl_step_l`, `sl_br_if_st`, `sl_if_st`, `sl_block_st`, `sl_loop_st`,
`sl_br_st`, `sl_nil_st` and `sl_pre_l`. The entailments are written out
(lists and values compared elementwise, ∃s with an equation solved) and
closed by rewriting with the assumptions when they can be; what is left
are the verification conditions: an invariant on entry and again, the
postcondition at exit, and side conditions such as an array element's
address. `vcs` has one tactic for each, in order (a mismatch lists them).
So `example_sum` is its code, its invariant and three one-line arithmetic
proofs. A `block`, `if` or `loop` with more code after it takes the state
after it from `afters` (`sl_cons_l`). If a tactic fails, the error lists
each condition with what its tactic left.

Arrays by index: `st_arr_load_at` and `st_arr_store_at` read and write the
element at `p + j * 4` of the whole array `arr(val(p), xs)`, as
`EL(val(j), xs)` and `list_update(xs, val(j), x)`, if `val(j) <
LENGTH(xs)` and the array ends below 2^32 (`addr_at`).

`example_insertion_sort` (`logic/example_sort.mbt`) sorts n words at p by
their unsigned values, with two nested loops (the inner one moves the
larger words right, holding the new one aside, and leaves by `br_if 1`
from the middle of its body): from locals `[p, n, 0, 0, 0]` and words xs
(if `val(p) + 4n < 2^32`) it leaves words ys with `sorted(ys)` (`PAIRWISE`
of `≤` on their values) and `perm(ys, xs)` (each value as often, by
`FILTER`). sym_prove leaves twelve conditions; each is one of the
`isort_` lemmas (`isort_shift`: moving a word right keeps the invariant,
by `perm_swap`; `isort_next`: putting x back keeps the outer one, by
`sorted_insert`).

Calls (`logic/calls.mbt`, `frames.mbt`, `call_rule.mbt`). A call's meaning
depends on the store's function table, which the triples above do not see
(they hold for every store), so calls are verified with module triples:

- `has_call_b`, `has_call` (inductive): an instruction holds a `call` or
  `call_indirect` at any depth (or is an `Invoke` or a `Frame`, which only
  come from calls); `call_free(es)`: none does. `call_free_step`: a step of
  call-free code keeps the store's functions and the frame's instance, and
  leaves call-free code (by induction on the reduction rules);
- `sl_triple_m(fs, inst, p, bs, q, ls)`: `sl_triple_l` for the stores whose
  function table is fs, run in instance inst, before and after (`keep`).
  `sl_triple_m_of`: every `sl_triple_l` of call-free code is one (from
  `safel_keep`); `sl_seq_m`, `sl_conseq_m`;
- frames, as labels: `frame_steps` (a step of `vs0 ++ [Frame(m, f1, es)]` is
  a step of es in f1, or the frame leaving with es's values, a trap or a
  return's values), `return_stuck` (a return in contexts does not step by
  itself), `frame_safe` (the frame is safe while es is, and leaves with
  es's results);
- `call_step`, `invoke_step`: `call j` steps to `Invoke(sfunc_ind(inst,
  j))`, which takes the arguments off the stack and becomes the frame
  `Frame(m, Wframe(args ++ zeros, inst), [Label(m, NIL, body)])`;
  `call_safe` puts them together;
- `sl_call`: for function j of the module, native in instance inst, whose
  body is proved from locals `args ++ zs` (and an empty stack) to results
  Q (a br out of it also giving Q), `call j` takes the arguments (P) off
  the stack and leaves results (Q), the caller's locals and the rest of its
  stack as they were.

`example_call` (`logic/example_call.mbt`): with function 0 the doubling
function (`local.get 0; local.get 0; i32.add`, proved with `sym_prove` as
`double_body`), `call 0` with x on the stack leaves x + x.

Returns, recursion and calls in `sym_prove` (`logic/returns.mbt`,
`specs.mbt`):

- `safer(n, s, f, es, q, l, rq)`: as `safel`, and a run may also stop at a
  `return`, with the return assertion rq holding of the values it returns.
  Sequencing (`safer_seq`) and labels (`safer_label`) pass a return on to
  the code around them, and a frame takes it (`frame_safe_r`: the frame
  leaves with a return's values, as with its body's);
- function specs: a set G of triples (a, P, Q), "the function at address a,
  from arguments with P, returns results with Q". `specs_ok(n, G, fs,
  inst)`: calling each of them is safe for n steps or fewer;
- `sl_triple_g(G, fs, inst, rp, p, bs, q, ls)`: the module triple with
  labels ls and return assertion rp, for every n where G's specs hold for n
  steps. It has the rules of `sl_triple_l`, for code with calls:
  `sl_seq_g`, `sl_conseq_g`, `sl_block_g`, `sl_loop_g`, `sl_if_g`,
  `sl_br_if_g`, `sl_br_g`, `sl_ex_g`, `sl_pure_g`, and `sl_return_g` (a
  `return` with rp of its values). `sl_triple_g_of` brings in any triple of
  call-free code;
- `sl_call_g`: `call j` with a spec of G for its function takes the
  arguments (P) and leaves the results (Q); `sl_funs_g`: G's specs hold for
  every n when each function's body has its triple, which may itself call
  the functions of G (recursion: a call takes a step before its body runs,
  so the induction on n goes through). `sl_triple_m_of_g` drops G again;
- `sym_prove` runs code in g triples too: a call by a spec (its arguments
  matched against the stack, its frame R the state's), `return` by an
  entailment to rp, and everything else as before (`sl_call_st_g`,
  `sl_return_st_g`, and the `_g` versions of the rules above). A spec
  whose variables cannot be read off the state (an array's parts) is
  given for each call in `calls` (a spec theorem and the terms for its
  ∀s): the call leaves P of the arguments to prove, and the code after it
  starts from Q (`sl_call_spec_g`).

`example_fact` (`logic/example_fact.mbt`): factorial, recursive, with an
early return:

```wat
(func $fact (param i32) (result i32)
  local.get 0
  i32.eqz
  if
    i32.const 1
    return
  end
  local.get 0
  local.get 0
  i32.const 1
  i32.sub
  call $fact
  i32.mul)
```

`sym_prove` runs the body (`fact_body`), its recursive call by the
function's own spec (`fact_spec`: from x, the result `fact_w(val(x))`),
and leaves two arithmetic conditions; `sl_funs_g` gives the spec
(`fact_specs`), and `example_fact` is `call 0` from x as a module triple.
`example_quicksort` (`logic/example_qsort.mbt`): quicksort, recursive,
with Lomuto's partition as a second function. From n words xs at p (if
`val(p) + 4n < 2^32`), `call 0` with `p, 0, n` on the stack leaves words ys
there with `sorted(ys)` and `perm(ys, xs)`. The specs are about a segment:
from the words `A ++ B ++ Cs` at p, with `|A| = lo` and `|A ++ B| = hi`,
quicksort leaves `A ++ ys ++ Cs`, and partition leaves `A ++ L ++ [pv] ++ G
++ Cs` (L below the pivot pv, G not). The partition's loop is proved by
`sym_prove` as call-free code (15 conditions, one tactic each), quicksort's
body by `sym_prove` as a g triple with its three calls, whose specs'
variables (the array's parts) are given for each call (`calls`), leaving
five conditions. `sl_funs_g` proves both specs at once.

Not yet: `call_indirect`, functions of other modules, host functions.

Control flow (`logic/labels.mbt`, `block.mbt`, `loop.mbt`) uses triples
with label assertions, innermost first:

- `safel(n, s, f, es, q, l)`: as `safe`, and a run may also stop at a br
  that leaves es, to the i-th label around it, with the i-th assertion of
  l holding of the values it takes; `triple_l`, `sl_triple_l` (labels
  lifted with the same frame). `sl_triple_l_of` carries every rule above
  over to them, and `sl_seq_l` sequences them. `sl_conseq_l` weakens the
  postcondition and, pointwise, the label assertions (`safel_mono`), and
  `sl_frame_l` adds a frame to the pre- and postcondition and every label;
- `sl_br`: `br i` with the i-th label assertion of its values;
- `sl_block`: for `block` with no parameters (block type `Tbv(ot)`): if the
  body is safe from an empty stack with postcondition qb and label 0
  assertion lb (of the block's arity), the block leaves its stack vs0 with
  `vs0 ++ r`, qb or lb of r;
- `sl_br_if`, `sl_if` (`logic/conditionals.mbt`): with an i32 c on the
  stack, `br_if i` is `br i` when c ≠ 0 and nothing when c = 0, and
  `if tb bs1 bs2` is `block tb bs1` or `block tb bs2`: each rule takes a
  triple (or, for `br_if` with c = 0, an entailment) for the case it steps
  to. `sl_if` holds for any block type;
- `sl_loop`: for `loop` with no parameters: with an invariant on the
  locals, globals and memory that holds on entry and is what a `br 0` must
  re-establish (with no values), the loop leaves `vs0 ++ r` with the body's
  postcondition of r.

Their proofs: `label_steps` (a step of `vs0 ++ [Label(m, e0, li)]` is a
step of li inside, or the label leaving with values, a trap or a br to it),
`br_unique` (a br's place is unique), `br_stuck` (a br to a label outside
does not step), `label_safe` (safety through a label, by induction on n),
and for loops `safel_down` (the run after a br 0 is the loop again, with
fewer steps). [PLAN.md](PLAN.md) says what comes next.

## Tests

`moon test` in a workspace tests every member, hol_light included, so
select the package. Its tests need a larger stack than the default. The
module's preferred target is wasm-gc, by far the fastest here (the logic's
tests take about a minute), so `--target` can be left out:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/wasm --target wasm-gc
```

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/logic --target wasm-gc
```
