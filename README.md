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

They are snapshot tests (`theory_test.mbt`): a test fails when the file no
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
  the locals and the globals (`gvals(s, f)`: the instance's globals by
  index), and the triple holds with any frame beside them on the
  instance's memory (`lift`). `lift` also asks that the instance's global
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
- `sl_unop` (`app_unop`), `sl_nop` (`sl_triple(p, [Nop], p)`), `sl_drop`
  and `sl_select` (of numbers: `select` keeps c1 if the i32 b is not 0,
  else c2);
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

`logic/examples.mbt` and `logic/example_sum.mbt` verify programs with the
rules alone, gluing rule instances with `sl_seq` and `sl_conseq`: `example_store_load` says that
`[i32.const k; i32.const v; i32.store; i32.const k; i32.load]`, from
`pts(val(k) + off, bs) * p` (bs 4 bytes), ends with v on the stack and
`pts(val(k) + off, serialise_i32(v)) * p` (`deserialise_serialise_i32`:
loading back what was stored gives the value). `example_sum` verifies a
loop on locals: from locals `[n0, acc0]`,

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
globals and memory) as they were. Its straight-line code uses the rules on
exact states (`logic/state.mbt`): `st(v, l, R)` says the stack is v, the
locals l and R holds of the globals and heap, and the `st_` rules (from the
rules above) step from one exact state to the next, written out by `norm`.
The loop's invariant goes into the body's precondition with `sl_pure_l`
and `sl_ex_l` (a pure fact or an `∃` out of a precondition), the empty
`else` is `sl_nil_l`, and `sl_triple_of_l` drops the empty list of labels
at the end.

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
select the package. Its tests need a larger stack than the default:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/wasm --target wasm-gc
```

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/logic --target wasm-gc
```
