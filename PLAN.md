# Plan: a separation logic for WebAssembly

How this project is built, where it stands, and what to do next. The README
says how to build and use it. What is proved so far is listed in
[logic/\_\_snapshot\_\_/theory.md](logic/__snapshot__/theory.md) and
[wasm/\_\_snapshot\_\_/theory.md](wasm/__snapshot__/theory.md).

## Goal

Prove things about real WebAssembly programs that use linear memory, in HOL
Light, trusting only the kernel and the definition of WebAssembly. The aim is
practical verification, such as `memcpy` or code from a compiler, rather than
a general logic of concurrency.

Not goals: an Iris port (`iProp`, step-indexed ghost state, an Iris proof
mode), threads, wasm-gc. Floats and SIMD are out of scope until integer
programs work end to end.

## Design

```
5. Programs       examples.mbt: rule instances glued together
4. Program logic  triple.mbt, seq.mbt, rules.mbt, labels.mbt, block.mbt, loop.mbt
3. Memory model   heap.mbt, memory.mbt
2. Semantics      package wasm: AST, reduce (WasmCert-Isabelle port), evaluator
1. HOL Light      hol-light.mbt: the kernel
```

**What is trusted.** The kernel and the definition of `reduce` in package
`wasm`. Everything in package `logic` is a theorem from them, and
`check_axioms` tests that no axiom was added. A mistake in the port of `reduce`
would invalidate every proof, so the evaluator checks the definition against
the official spec testsuite (`wasm/spec_test.mbt`).

**Decisions, and why:**

- **Memory is a partial heap.** `heap_of(m)` views a memory's bytes as
  `(Num) -> Option[Byte]`, `pts(a, bs)` is exactly the bytes `bs` at `a`, and
  `star` is disjoint union. `load_pts` and `store_pts` connect them to
  WasmCert's `load` and `store`.
- **Partial correctness, no traps, over all runs.** `safe(n, ...)` is defined
  by recursion on the steps left, and a triple means safe for every `n`. No
  determinism proof is needed, which matters because `memory.grow` is
  nondeterministic. Termination is not claimed.
- **The frame is built in.** `sl_triple` quantifies over a frame `r` on the
  memory (`lift`), so the frame rule follows from `star_assoc`.
- **Stack, locals and globals are plain data.** Assertions (`SAssn`) take the
  value stack, the locals and the globals (`gvals(s, f)`, the instance's
  globals by index) as arguments. Only memory uses `star`. `lift` also asks
  that the instance's global addresses are in the store and distinct
  (`globs_ok`), so `global.set` changes exactly one entry.
- **Structured control flow, in the style of Wasm Logic** (Watt et al., ECOOP
  2019). `sl_triple_l` has one assertion per enclosing label, innermost first.
  A `br` state counts as finished if its label's assertion holds.
- **Rules are proved, not assumed.** There is no separate "logic" that needs a
  soundness theorem: each rule is a theorem about `reduce`.
- **Generated theory listings.** Statements are strings inside tactic code, so
  `listing()` prints them in order and a snapshot test keeps the file honest.

## Status

| Piece | State |
|---|---|
| Semantics, typing relations (ported from WasmCert-Isabelle) | done |
| Evaluator: integers, control, locals, globals, calls, memory | done |
| Spec checks: `i32.wast`, `i64.wast`, loads of `address.wast` at address 0 | done |
| Memory model, `load_pts`, `store_pts` | done |
| `sl_conseq`, `sl_frame`, `sl_seq`, `sl_const`, `sl_binop` | done |
| `sl_load_i32`, `sl_store_i32` | done |
| `sl_seq_l`, `sl_br`, `sl_block`, `sl_loop` | done |
| `sl_conseq_l`, `sl_frame_l` (from `safel_mono`) | done |
| Globals in assertions; `sl_global_get`, `sl_global_set` | done |
| `sl_local_get`, `sl_local_set`, `sl_local_tee` | done |
| `sl_br_if`, `sl_if` | done |
| `sl_ex_l`, `sl_pure_l`, `sl_nil_l`, `sl_triple_of_l`, `pts_split` | done |
| Exact-state rules (`st`, `st_const`, `st_binop`, `st_local_get`, `st_local_set`) | done |
| Verified programs: `example_store_load`, `example_sum` (a loop) | done |
| Arrays: `arr`, `arr_split`, `arr_focus`, `st_arr_store`, `st_arr_load` | done |
| `example_fill` (a loop over memory) | done |
| `sl_testop`, `sl_relop`, `st_testop`, `st_relop` | done |
| `example_array_sum` (reads an array, a comparison as loop condition) | done |
| `sl_unop`, `sl_nop`, `sl_drop`, `sl_select`, `sl_load_i64`, `sl_store_i64` | done |
| Everything under "Next steps" | not started |

Known limits of what exists:

- `sl_block` and `sl_loop` cover only block types `Tbv(ot)`, with no parameters.
- `sl_global_set`, `sl_local_set` and `sl_local_tee` take a number (`V_num`),
  not a reference, as their operand. Triples assume
  `globs_ok`, so a module that imports one global twice is not covered.
- The evaluator computes on memory byte by byte, so it suits small memories.
  The spec cases that test the end of a 64 KiB page are not covered.
- The builder lacks `extend8_s`, `extend16_s` and `extend32_s`, so their spec
  cases are left out.
- WasmCert's soundness proofs (`Wasm_Properties`, `Wasm_Soundness`) are not
  ported. Nothing here depends on them.

### What the first loops showed

About the rules' shapes, from `example_sum` and `example_fill`:

- The instruction rules' "operands on top of some vs0" form does not glue
  by itself: each step needs an entailment. The exact-state `st_` rules
  and `norm` (state.mbt) made straight-line code glue with `sl_seq` alone;
  this is what the automation step should build on.
- `sl_br_if` and `sl_if` fix the condition, so the body is proved for
  each value and `sl_pure_l`, `sl_ex_l` put the invariant's facts and
  values back into the precondition. That worked without changing them.
- `sl_loop` and `sl_block` take their label assertions literally, so build
  the rule instance first and read the label from it (as example_sum
  does) rather than writing it again.
- The array rules take the array split at the element (`ys ++ [x] ++ zs`),
  so a loop that walks an array keeps the walked part and the rest in its
  invariant, and no star rearranging is left to the loop's proof.
- Arithmetic and list facts about the loop's state are best proved as
  lemmas first (`fill_step`, `fill_exit`), so the loop proof only applies
  them.
- A comparison computes to `wasm_bool(word_ult(i, n))`; `wasm_bool_zero`
  turns `sl_br_if`'s and `sl_if`'s cases on it into the comparison itself.
- An invariant that names a fixed value of the specification (the array
  `xs` in `example_array_sum`) puts it in the loop's label too: do not
  rewrite or substitute it in a goal that still holds the labels.

## Next steps

In order. Each can be merged on its own. "Done when" means the named theorems
appear in `theory.md`, with the tests passing.

1. **More instructions.** `unop`, `nop`, `drop`, `select` and the i64 loads
   and stores are done. Left:
   - Packed loads and stores (`i32.load8_u`, `i32.store8`, ...): the
     reduction rules use `load_packed` and `store_packed`, so they need
     `load_pts`/`store_pts` for them, then the recipe below.
   - `cvtop` (`i32.wrap_i64`, `i64.extend_i32_s/u`): `cvt` gives an option,
     as `app_binop` does, so the rule takes `cvt(...) == SOME(c)`.
   - `memory.size` and `memory.grow` need a design decision: an assertion
     sees the memory only as a heap, not its size. Add the size as a further
     plain-data argument of `lift` (as globals are), or a points-to for "the
     memory has n pages". `memory.grow` then gains `pts(old length, zeros)`,
     with the failure case returning `-1`.
   - `drop` and `select` take numbers (`V_num`), like `global.set`: values in
     general need `is_val(v_to_e(v))` in `prove_prefix`.

2. **Automation.** A symbolic-execution tactic.
   - The `st_` rules and `norm` already glue straight-line code with no
     entailments. Generalize them: walk the instruction list, pick the rule for
     each instruction, find the frame by matching `star` terms, and leave only
     the loop invariants and real side conditions.
   - Measure early on a program of about 100 instructions, because terms grow
     and the tests already need a large stack.
   - Done when: the proofs of `example_sum`, `example_fill` and
     `example_array_sum` are a few lines each.

3. **Sorting.** Insertion sort of an i32 array in linear memory, written by
   hand: two nested loops, comparisons, array loads and stores.
   - Specify it: `sorted(ys)` (by signed or unsigned word order, as the
     program compares) and `perm(xs, ys)` (a permutation), with the lemmas
     that a shift or a swap keeps a permutation.
   - Invariants: the outer loop keeps the prefix sorted and the whole array a
     permutation of the input; the inner loop shifts larger elements right.
   - An element by index (`arr` at `i`, from `split_at`) is needed here.
   - Done when: `example_insertion_sort`.

4. **Calls.** `sl_call`, with per-function specs.
   - A `Frame` needs its own step inversion, like `label_steps`. `return` needs
     its own postcondition: add a return assertion as a further `safel` argument,
     as Wasm Logic does, rather than treating it as a label.
   - Recursive functions: induction on the steps left, as in `sl_loop`.

5. **Real programs.** An untrusted `.wat` or `.wasm` importer that makes programs
   through the builder, then verify a function from a compiled module (a sort
   from a C compiler is a good target: it adds a stack pointer global, its own
   stack frame in memory, and more instructions). The theorem is about the
   imported term, so the importer is trusted to match the file until someone
   verifies a decoder.

Separately, at any time: more spec coverage (block, loop, `br_table`, the
`extend*_s` operators), since this checks the one thing the proofs rest on.

## Working on it

Build and test commands are in the README. After changing what a package defines
or proves, regenerate the listings and read the diff:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/logic --target wasm-gc --update
```

Add a new theorem you rely on to the list in `logic/logic_test.mbt`.

### Adding an instruction rule

`rules.mbt` has the pattern, for an instruction `x` with operands `ops`:

1. `prove_arities(name, x, n)`: the base step of `x` takes exactly `n` values.
   This is what keeps the stack below the operands untouched.
2. `prove_prefix(name, ops, x, arity)`: a step of `vs0 ++ ops ++ [x]` is a step
   of `ops ++ [x]`, with `vs0` left alone.
3. `@wasm.step_cases(s, f, ops ++ [x])`: what that step can be. Pass
   `compute=false` to keep functions like `store` in the side conditions.
4. The rule. If `x` leaves the store and frame alone and pushes one number
   (or nothing: pass `step="(NIL : List[Einstr])"`), use `prove_value_rule`.
   If it pushes any value or changes the store or frame, copy
   `sl_global_get` or `sl_local_set`: prove `<x>_step` (the step exists)
   and `<x>_cases` (the only steps), for any state, first, and the rule's
   proof then follows `prove_value_rule`'s shape.

The reduction rules are referred to by position in `reduce_rule_texts()`
(`reduce_base` has the same rules without the context rule, at index 38).

### Debugging a proof

- A failed proof raises, and loading prints `wasmcert/logic: loading failed: ...`.
- To see goals, add a whitebox test that sets `trace.val = true` and calls
  `load()`. `lemma` then names each lemma and prints the goals left over, and
  `show_goal("label")` inside a tactic prints the goal there. Remove the test
  afterwards.
- Output is buffered until the process exits, so a hang shows nothing. Run under
  `timeout` and redirect to a file.

### Things that will catch you out

Proof search:

- MESON can run for a very long time before failing, so calling it speculatively
  is expensive. Use it on small goals, with a short lemma list. Lists with big
  distinctness theorems have overflowed the stack.
- MESON does not reassociate appends: `vs0 ++ [x, y]` does not unify with
  `xs ++ [y]` ("solve_goal: Too deep"). `entails` and `then_rule` rewrite
  stacks to `vs0 ++ [x, y]` by default; pass `reassoc=false` when the target
  is written `(vs0 ++ [x]) ++ [y]`.
- `@tactics.first` takes the first alternative that does not fail, even if it
  leaves goals. Wrap alternatives in `solve`. When the cases are known, prefer
  `thenl` with one tactic per case: it is faster and fails more clearly.

Tactics:

- `strip_tac` also splits a conjunction in the goal, so a following `conj_tac`
  fails. Use `disch_then` with `strip_assume_tac` to keep the goal whole.
- `seq` runs each tactic on all goals. To treat goals differently, use `thenl`.
- `struct_cases_tac` substitutes only in the goal. To reach the assumptions, use
  `disj_cases_tac` and then `subst_vars`.
- `@lists.list_induct_tac` names the head and tail `h` and `t`.
- `@tactics.prove` refuses a theorem with hypotheses ("additional assumptions
  in result"): put them in the goal as antecedents and discharge them after
  (`conseq_l`'s `hyps`).
- `match_mp_tac(th)` fails when the tactic is built, not run, if `th` is not
  an implication, so `first` and `solve` around it do not catch it.
- `first_x_assum` tries every assumption, so the error you see may come from
  another assumption, and a tracing wrapper will report harmless failures.
- `prove_value_rule` names the step count `n`: a rule with its own variable
  `n` fails at `disj2_tac` (`sl_select` calls its condition `b`).
- `subst_vars` can substitute in an unwanted direction: `NIL == suf` replaced
  `NIL` by `suf`, and `LENGTH(vs) == m` replaces `m`. Orient equations first
  (`nil_eq_sym`), or substitute before adding such facts.
- `spec` fails on polymorphic theorems such as `list_cases`: use `ispec`.

Rewriting:

- `@lists.append_assoc()` rewrites to the left-nested form. Use its `gsym` for
  the right-nested one.
- Rewriting with both a theorem and its `gsym` loops, and the result is a stack
  overflow (a trap, not a catchable error).
- `FUN_EQ_THM` rewrites every function equality in the goal, including premises
  such as `h == hunion(...)`. To prove two lambdas equal, use `abs_tac` instead.
- Numeral arithmetic can collapse a rule with a false premise to `⊢ T`, so apply
  conversions to its parts (`apply_rule` in `wasm/eval.mbt`).

Syntax and names:

- `f(x : T)` does not parse: write `f((x : T))`. `(NIL : List[T])` needs its
  parentheses. `∃` after `→` needs parentheses.
- `MOD` and `EXP` are written as functions: `MOD(n, EXP(256, k))`.
- HOL constants take priority over variables: `inv` is real inverse, so a variable
  named `inv` gives a confusing type error.
- `const` and `loop` are MoonBit keywords.
- A rule's `∃`s after `match_mp_tac` come in the rule's variable order, which
  need not be the order you expect.
- `fn(g) { ... }` that raises is deprecated. Use `g => { ... }`.

Costs: loading `logic` re-proves everything, about three minutes for its
tests on `wasm-gc`. There is no theorem cache.
