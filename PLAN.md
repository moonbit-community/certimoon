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
4. Program logic  triple.mbt, seq.mbt, rules.mbt, labels.mbt, block.mbt, loop.mbt,
                  sym.mbt; calls.mbt, frames.mbt, call_rule.mbt, returns.mbt, specs.mbt
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
- **Stack, locals, globals and the memory's length are plain data.**
  Assertions (`SAssn`) take the value stack, the locals, the globals
  (`gvals(s, f)`, the instance's globals by index) and the memory's length
  in bytes (`mem_length`, from which `memory.size` is the length in pages)
  as arguments. Only the memory's bytes use `star`. `lift` also asks
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
| The memory's length in assertions; `sl_memory_size`, `sl_memory_grow` | done |
| `sl_convert`, `sl_reinterpret` (cvtop) | done |
| Packed loads and stores: `sl_load_packed_i32/i64`, `sl_store_packed_i32/i64` | done |
| `sl_drop`, `sl_select` of any values (`value_cases`) | done |
| Symbolic execution: `sym_tac`, `sym_prove`; the loop examples use it | done |
| `example_insertion_sort`; array rules by index; states after a block | done |
| Calls: call-free code, module triples, frames, `sl_call`, `example_call` | done |
| Returns (`safer`), function specs and recursion (`sl_triple_g`, `sl_funs_g`), calls in `sym_prove`, `example_fact` | done |
| Everything else under "Next steps" | not started |

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
  the rule instance first and read the label from it (as sl_loop_st
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

About the automation (`sym.mbt`):

- It works backwards from the goal and rewrites only the precondition, so
  the postcondition and the labels stay as the rules made them, and the
  rule instances (`sl_loop`, `sl_block`) are built once, in `sl_loop_st`
  and `sl_block_st`, rather than in each proof.
- A straight-line rule is instantiated forwards, by matching its
  precondition against the state with the stack split at its operands
  (`split_stack`); its result (`app_binop`) is then computed, so the rule
  needs no hypothesis about it.
- Reshaping a loop invariant with MESON cost over a million inferences per
  loop. Pulling the ∃s to the front by rewriting, taking them with
  `sl_ex_l`, and then rearranging the conjuncts by rewriting with the
  assumptions is immediate.

## Next steps

In order. Each can be merged on its own. "Done when" means the named theorems
appear in `theory.md`, with the tests passing.

1. **More instructions.** Done: `unop`, `nop`, `drop` and `select` (of any
   values), the i64 and packed loads and stores, `memory.size`,
   `memory.grow` and `cvtop`. The step is done. What a later step may want:
   `global.set` and `local.set` of any values (by `value_cases`, as `drop`),
   and lemmas that simplify packed loads (`deserialise_i32(sign_extend(...))`).

2. **Automation.** Done: `sym_tac` and `sym_prove` (`logic/sym.mbt`) run
   straight-line code with the `st_` rules, go into `br_if`, `if`, `block`
   and `loop`, and leave the verification conditions, written out and
   simplified. `example_sum`, `example_fill` and `example_array_sum` are now
   their code, their invariant and one short tactic per condition. What a
   later step will want:
   - `br` to a block with results, and values on a `br`'s label other than
     none; `local.tee`, `global.get`/`set`, `drop`, `select` and the other
     loads and stores as `st_` rules (`step_rules` lists what it knows).
   - Measured on straight-line code (`local.get; i32.const; i32.add;
     local.set`, repeated) on the native target: 20 instructions in 0.1 s,
     100 in 0.6 s, so a long program is not the problem; loading is.

3. **Sorting.** Done: `example_insertion_sort` (`logic/example_sort.mbt`),
   insertion sort by unsigned value, with `sorted` (`PAIRWISE`) and `perm`
   (equal `FILTER` counts). It needed the array rules by index
   (`st_arr_load_at`, `st_arr_store_at`) and states after a block with more
   code after it (`afters`, `sl_cons_l`). What a later step may want:
   signed order (`i32.le_s`, `word_ile`), and a library of list lemmas
   instead of the `isort_` ones written for this proof.

4. **Calls.** Done, except `call_indirect`: `sl_call` (`logic/call_rule.mbt`)
   for a call of a function of the same module given its body's spec, on
   module triples (`sl_triple_m`, calls.mbt) and frames (frames.mbt); then
   (`logic/returns.mbt`, `logic/specs.mbt`):
   - `return`: `safer`, safel with a return assertion; a frame takes a
     return with its values (`frame_safe_r`).
   - Recursion: g triples `sl_triple_g(G, fs, inst, rp, ...)` hold for n
     steps when the function specs G do; `sl_funs_g` proves G's specs from
     their bodies' g triples by induction on n, so a body may call its own
     function (or any of G's).
   - The structural rules for g triples (seq, conseq, block, loop, if,
     br_if, br, ex, pure, return, call), and `sym_prove` on g triples, a
     call by a spec theorem `∀ xs. G(a, P, Q)` whose P is `args == [..] &&
     R(gs, ms, h)` (the state's R is used as the frame).
   - `example_fact`: recursive factorial with an early return.

   Still to do:
   - `call_indirect`. The target comes from a table in the store, which
     the triples do not fix (code without calls may write tables). Plan:
     keep the tables fixed in g triples as well as the functions, and
     carry over only call-free code with no table writes (a predicate like
     `call_free`, and its step lemma like `call_free_step`). Then
     `call_indirect` with the table's entry for c is `call` of that
     function, if its type is the one asked for.
   - Functions of other modules: a spec's P and Q are about the caller's
     instance (its globals and memory), so a callee in another instance
     needs specs about that instance's state.
   - Host functions are not provable as they are: WasmCert lets a host call
     trap in any state (`reduce` has a rule from any host invoke to
     `[Trap]`), so no triple of a host call holds. Covering them would mean
     assuming more about the host.
   - Calls in sym_prove whose spec frames memory (P not of the form
     `args == [..] && R(...)`): use sl_call_g and sl_conseq_g by hand.
   - Loops with calls in sym_prove are untested (sl_loop_st_g is proved
     but no example uses it).

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
  distinctness theorems have overflowed the stack. `first([meson, ...])`
  over many goals runs it to failure on each goal it does not fit:
  `reduce_imp_decomp` took 106 s that way and 0.6 s with one tactic per
  case (`thenl`), and `length_drop` 39 s until arithmetic was tried first.
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
  `disj_cases_tac` and then `subst_vars`, or move the assumption into the
  goal first (`cases_n_specs` in specs.mbt does that for `specs_ok(n)`).
- `subst_vars` also substitutes away the module's fs and inst when an
  assumption says `s_funcs(s) == fs`: specs.mbt keeps these facts as one
  `in_mod(fs, inst, s, f)` (`keep_in_mod`) so that it does not.
- `match_accept_tac` can run for very long on a big triple that does not
  match at once: `accept_tac` of the exact instance (`ispecl`) instead.
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
- `step_cases` takes only written-out values. For operands of any value,
  write them `v_to_e((v : Value))` and get the cases from `value_cases`,
  which splits each v into its three kinds; `prove_prefix` knows
  `is_val(v_to_e(v))`.
- A rule over a pair in the instruction (`Load(t, SOME((tp, sx)), ...)`)
  needs `pair_eq` in `unfold`. Its case's memory index is equated with the
  precondition's only by the last `strip_tac`, so `again=true` rewrites the
  case's condition after it; `subst_vars` then names the index `j'`.
- A `prove_value_rule` hypothesis `e == x`, with x a variable of the code,
  lets `subst_vars` remove x from the goal but not from the code, so the
  step no longer matches. Prove the rule with e in the code, then derive it
  (`sl_reinterpret` from `reinterpret_typeof`). A conjunction is safe
  (`sl_convert`).
- `subst_vars` can substitute in an unwanted direction: `NIL == suf` replaced
  `NIL` by `suf`, and `LENGTH(vs) == m` replaces `m`. Orient equations first
  (`nil_eq_sym`), or substitute before adding such facts.
- `spec` fails on polymorphic theorems such as `list_cases`: use `ispec`.
- `repeat_tac(cond_cases_tac)` keeps splitting conditions already decided
  (leaving goals with `!true` among the assumptions). Split on the
  conditions themselves with `asm_cases_tac`, then rewrite.

Rewriting:

- `top_depth_conv` repeats its conversion until it fails, and a rewriting
  conversion never fails, so `top_depth_conv(rewrite_conv(...))` never
  stops (a stack overflow). Rewriting conversions already go to the end.
- Matching `p(vs, lc, gs, ms, h)` against `st(v, l, R)(vs, lc, gs, ms, h)`
  binds p to the η-expanded `λ vs ... . st(...)(vs, ...)`, so an
  assumption about `st(v, l, R)` no longer matches: rewrite with
  `@class.eta_ax()` first.
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
  named `inv` gives a confusing type error. Bound variables named after
  constants (`S`, `T`) are renamed (`S'`), so a term mentioning them
  afterwards no longer matches.
- A failing `ABS` (or another kernel rule) can come from a tactic run much
  earlier: the justifications run at the end. One cause: a theorem made with
  `assume_rule` of a term that is not one of the goal's assumptions (a
  conjunction of three of them is not), so its hypothesis stays and the final
  `GEN` fails.
- Instantiating a lemma's free variable with a goal variable of the same name
  as one of the lemma's bound variables (`f0 := f` under `∀ f`) made
  `match_mp_tac` fail: name bound variables apart (`s2`, `f2`).
- A variable whose type only a binder fixes (`x` in `fact_w(val(x))`)
  gets a type variable in a term written alone (an `exists_tac` term), and
  then does not match the theorem's `x`; annotate it (`(x : W32)`).
- "Warning: inventing type variables" means a term has an unfixed type:
  `val(word(1))` is a word of any size. Annotate it (`(word(1) : W32)`).
- `const` and `loop` are MoonBit keywords.
- A rule's `∃`s after `match_mp_tac` come in the rule's variable order, which
  need not be the order you expect.
- `fn(g) { ... }` that raises is deprecated. Use `g => { ... }`.

Do not run `moon fmt`: moon.work makes `../hol-light.mbt` a member, so it
reformats that repository too, and the current version crashed halfway
(November 2026), leaving both reformatted and hol-light.mbt not compiling.

Costs: loading `logic` re-proves everything; there is no theorem cache.
On wasm-gc, the module's preferred target, `moon test -p
moonbit-community/wasmcert/logic` takes about a minute (November 2026),
and rebuilding after a change a few seconds. Of a load: HOL Light's core
and its words library about 20 s, the WasmCert definitions and facts 15 s,
the logic 20 s, most of that in `step_cases` (expanding `reduce_base`'s
40 cases for each way of splitting the operands; giving it the
instruction's arity would avoid the split). The `wasm` and `native`
targets are three to five times slower; `native --release` halves
native's time but rebuilds the whole program, two minutes, after any
change. Each test file is its own process and loads the logic again, so
the logic's tests are all in `logic_test.mbt`. Run one file with `moon
test logic/logic_test.mbt` (`-f` filters test names, not files); `-p
logic` alone also runs hol_light's own `logic` package. To find what is
slow, time `lemma` and `section` with `@env.now()` from a temporary
whitebox test. On native (`ulimit -s 65520` too), a crash loses the
buffered output: run the test executable under `lldb` (its argument is
`logic_test.mbt:0-1`, the file and the tests' range) for a backtrace, or
`sample` it for a profile.
