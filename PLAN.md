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
- **Stack and locals are plain data.** Assertions (`SAssn`) take the value
  stack and the locals as arguments. Only memory uses `star`.
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
| One verified program: `example_store_load` | done |
| Everything under "Next steps" | not started |

Known limits of what exists:

- `sl_block` and `sl_loop` cover only block types `Tbv(ot)`, with no parameters.
- `sl_conseq` and `sl_frame` exist for `sl_triple`, not yet for `sl_triple_l`.
- The evaluator computes on memory byte by byte, so it suits small memories.
  The spec cases that test the end of a 64 KiB page are not covered.
- The builder lacks `extend8_s`, `extend16_s` and `extend32_s`, so their spec
  cases are left out.
- WasmCert's soundness proofs (`Wasm_Properties`, `Wasm_Soundness`) are not
  ported. Nothing here depends on them.

## Next steps

In order. Each can be merged on its own. "Done when" means the named theorems
appear in `theory.md`, with the tests passing.

1. **Structural rules with labels.** The rules that follow all need these.
   - `safel_mono` (monotone in the postcondition and, pointwise, in the labels),
     then `sl_conseq_l` and `sl_frame_l`. For the frame, labels get the frame
     too: use `lift_frame` under `MAP`, with `@lists.map_o()`.
   - Done when: `sl_conseq_l`, `sl_frame_l`.

2. **Globals.** `SAssn` has no argument for them, so this is a design change.
   - Add globals to `lift` as a further plain-data argument, as locals are. This
     changes the statement of every rule once, so do it now, while there are
     about a dozen rules, and before the locals rules are written.
   - Then `sl_global_get` and `sl_global_set`, which read and write the store
     through the instance's global addresses.
   - Done when: every existing rule is restated with globals, and the two rules.

3. **Locals.** `sl_local_get`, `sl_local_set`, `sl_local_tee`.
   - `reduce` rule 8 needs `f_locs(f) == vi ++ [v] ++ vs`, and rule 9 needs the
     frame written as `Wframe(vi ++ [v] ++ vs, i)`, so split the locals list at
     `j` and case on `f`. Tee is `reduce_simple` rule 37: it steps to
     `[v, v, local.set]`, so prove it from the other two.
   - `prove_value_rule` assumes a `V_num` result, and `local.get` can push any
     value: generalize it, or write these rules directly as `sl_store_i32` does.
   - Done when: the three rules.

4. **Conditionals.** `sl_br_if`, `sl_if`.
   - `br_if` steps to `br i` or to nothing, depending on the condition (rules
     30, 31), and then `sl_br` applies. `if` steps to a `block` (rules 25, 26),
     and then `sl_block` applies.
   - So `sl_if` has `sl_block`'s limit: block types `Tbv(ot)` only. Add it to
     the known limits above.
   - Done when: both rules.

5. **First loops.** The test of whether the rules work together.
   - A counting loop on locals first (sum `1..n`), then one over memory, such as
     filling a region.
   - Comparisons (`relop`, `eqz`) and packed stores come in step 6, so write
     these loops without them. Count down and end the body with
     `local.get n; br_if 0`, which repeats while `n ≠ 0`; guard the loop with
     `if` for `n = 0`. Fill with `i32.store`, 4 bytes per iteration. If that
     turns out awkward, move `sl_relop` and `sl_testop` before this step.
   - Memory loops need `pts_split`: `pts(a, xs ++ ys)` is
     `star(pts(a, xs), pts(a + LENGTH(xs), ys))`. Not proved yet.
   - Word side conditions should go to `@words.word_rule` and
     `@words.word_arith_tac`.
   - Done when: `example_sum`, `example_fill`. Record any rule that turned out
     awkward to use: this is the point to change a rule's shape cheaply.

6. **More instructions.** Mechanical, using the recipe below.
   - `i64` and packed loads and stores, `unop`, `testop`, `relop`, `cvtop`,
     `drop`, `select`, `nop`, `memory.size`.
   - `memory.grow`: the heap gets bigger, so state the rule as gaining
     `pts(old length, zeros)`, with the failure case returning `-1`.

7. **Automation.** A symbolic-execution tactic.
   - Walk the instruction list, pick the rule for each instruction, find the
     frame by matching `star` terms, and leave only real side conditions.
     `then_rule` and `entails` in `examples.mbt` are the starting point.
   - Measure early on a program of about 100 instructions, because terms grow
     and the tests already need a large stack.
   - Done when: the proofs of step 5 are a few lines each.

8. **Calls.** `sl_call`, with per-function specs.
   - A `Frame` needs its own step inversion, like `label_steps`. `return` needs
     its own postcondition: add a return assertion as a further `safel` argument,
     as Wasm Logic does, rather than treating it as a label.
   - Recursive functions: induction on the steps left, as in `sl_loop`.

9. **Real programs.** An untrusted `.wat` or `.wasm` importer that makes programs
   through the builder, then verify a function from a compiled module. The theorem
   is about the imported term, so the importer is trusted to match the file until
   someone verifies a decoder.

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
4. The rule. If `x` leaves the store and frame alone and pushes one number, use
   `prove_value_rule`. Otherwise copy `prove_store_rule`.

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
- `@tactics.first` takes the first alternative that does not fail, even if it
  leaves goals. Wrap alternatives in `solve`. When the cases are known, prefer
  `thenl` with one tactic per case: it is faster and fails more clearly.

Tactics:

- `strip_tac` also splits a conjunction in the goal, so a following `conj_tac`
  fails. Use `disch_then` with `strip_assume_tac` to keep the goal whole.
- `seq` runs each tactic on all goals. To treat goals differently, use `thenl`.
- `struct_cases_tac` substitutes only in the goal. To reach the assumptions, use
  `disj_cases_tac` and then `subst_vars`.
- `first_x_assum` tries every assumption, so the error you see may come from
  another assumption, and a tracing wrapper will report harmless failures.
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

Costs: loading `logic` re-proves everything, about a minute and a half for its
tests on `wasm-gc`. There is no theorem cache.
