# Plan: a separation logic for WebAssembly

How this project is built, where it stands, and what to do next. The README
says how to build it and how to prove a program with it. What is proved so
far is listed in [logic/\_\_snapshot\_\_/theory.md](logic/__snapshot__/theory.md)
and [wasm/\_\_snapshot\_\_/theory.md](wasm/__snapshot__/theory.md).

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
5. Programs       example_*.mbt: verified programs; sym.mbt runs code
4. Program logic  triples (four layers, below), the instruction and control rules
3. Memory model   heap.mbt, memory.mbt, arrays.mbt
2. Semantics      package wasm: AST, reduce (WasmCert-Isabelle port), evaluator
1. HOL Light      hol-light.mbt: the kernel
```

**What is trusted.** The kernel and the definition of `reduce` in package
`wasm`. Everything in package `logic` is a theorem from them, and
`check_axioms` tests that no axiom was added. A mistake in the port of `reduce`
would invalidate every proof, so the evaluator checks the definition against
the official spec testsuite (`wasm/spec_test.mbt`).

**The triples, in layers.** Each adds what the one before cannot say, and
carries the one before over:

| Triple | Safety | Adds | Carried over by |
|---|---|---|---|
| `sl_triple(p, bs, q)` | `safe` | (the base) | |
| `sl_triple_l(p, bs, q, ls)` | `safel` | `br` out of the code, to label assertions | `sl_triple_l_of` |
| `sl_triple_m(fs, inst, p, bs, q, ls)` | `safel` | stores with function table fs, instance inst (`keep`) | `sl_triple_m_of` (call-free code) |
| `sl_triple_g(G, fs, inst, rp, p, bs, q, ls)` | `safer` | `return` (to rp), and specs G of the functions, assumed for n steps | `sl_triple_g_of_m` |

`sl_triple_m_of_g` goes back down when G's specs hold and rp is false. The
instruction rules exist once, for `sl_triple`; the control rules (block,
loop, if, br_if, br) twice, for `sl_triple_l` and for `sl_triple_g`, and
sym_prove's rules for both (`prove_sym_derived` makes them from the same
code). See "Next steps" for making that one layer.

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
  A `br` state counts as finished if its label's assertion holds; a
  `return`, in `safer`, if the return assertion does.
- **Calls through specs, by steps.** A call's meaning depends on the store's
  functions, so code with calls is proved for the stores whose function
  table is fs. A body may assume the specs G of the functions it calls,
  for the steps left (`sl_triple_g` holds for n steps when G's specs do):
  a call takes a step before its body runs, so induction on n
  (`sl_funs_g`) proves G's specs from their bodies, recursion included.
- **Rules are proved, not assumed.** There is no separate "logic" that needs a
  soundness theorem: each rule is a theorem about `reduce`.
- **Generated theory listings.** Statements are strings inside tactic code, so
  `listing()` prints them in order and a snapshot test keeps the file honest.

### Code map

Package `logic`, in the order `load()` proves it (init.mbt), which is a
good order to read it in:

| File | What it has |
|---|---|
| defs.mbt, tactics.mbt, listing.mbt | the theorem table (`thm`, `lemma`, `def`, `record`), tactic helpers, the theory listing |
| heap.mbt, memory.mbt | heaps, `star`, `pts`; loads and stores against points-to |
| triple.mbt, seq.mbt | `safe`, `triple`, `sl_triple`, `lift`; consequence, frame, sequencing |
| rules.mbt | the instruction rules and their pattern (`prove_arities`, `prove_prefix`, `prove_value_rule`) |
| labels.mbt, block.mbt, loop.mbt | `safel`, `sl_triple_l`; br, label steps, `label_safe`, block and loop rules |
| globals.mbt, memsize.mbt, locals.mbt, conditionals.mbt | globals, memory size and grow, locals, `br_if` and `if` |
| state.mbt, arrays.mbt | exact states `st` and the `st_` rules; `arr` and the array rules |
| sym.mbt | `sym_prove` and its rules (`prove_sym_derived`) |
| calls.mbt | call-free code (`has_call`, `call_free_step`), module triples (`sl_triple_m`, `keep`) |
| adequacy.mbt | what triples say about runs (`reduce_trans`): `sl_triple_adequate`, `sl_triple_m_adequate` |
| frames.mbt, call_rule.mbt | frame steps and safety, `return_stuck`; call and invoke steps, `sl_call` |
| returns.mbt | `safer`: safety with returns; its seq, label and frame lemmas |
| specs.mbt | function specs, `sl_triple_g` and its rules, `sl_call_g`, `sl_funs_g`, and sym's rules for it |
| examples.mbt, example_*.mbt | the verified programs |
| logic_test.mbt | the listing's snapshot, the theorems' list, the public API's test |

Package `wasm`: ast.mbt, numeric.mbt, store.mbt, typing.mbt, reduction.mbt
(the port; the header comments say where it differs from Isabelle),
defs.mbt (its plumbing), props.mbt (facts about `reduce`, `step_cases`),
eval.mbt and builder.mbt (the evaluator), and the tests.

## Status

| Piece | State |
|---|---|
| Semantics, typing relations (ported from WasmCert-Isabelle) | done |
| Evaluator: integers, control, locals, globals, calls, memory | done |
| Spec checks: `i32.wast`, `i64.wast`, loads of `address.wast` at address 0 | done |
| Memory model: heaps, points-to, arrays | done |
| Instruction rules: consts, unop, binop, testop, relop, cvtop, nop, drop, select, loads and stores (i32, i64, packed), memory.size and grow, globals, locals | done |
| Control: br, br_if, if, block and loop (no parameters), return | done |
| Calls of the module's functions, by specs, recursion included | done |
| Symbolic execution (`sym_prove`), for code without and with calls | done |
| Adequacy: `sl_triple` and `sl_triple_m` (no labels) stated with `reduce_trans` alone | done |
| Closed theorems: `fact_closed` (from `call 0` in a frame of the instance) | done; quicksort next |
| A public API for proofs in other packages | done |
| Examples: store/load, sum, fill, array sum, insertion sort, call, factorial, quicksort | done |
| `call_indirect`, functions of other modules or the host | not started |
| An importer for `.wat` / `.wasm`, and a compiled program | not started |

Known limits of what exists:

- `sl_block` and `sl_loop` cover only block types `Tbv(ot)`, with no parameters.
- `sl_global_set`, `sl_local_set` and `sl_local_tee` take a number (`V_num`),
  not a reference, as their operand. Triples assume
  `globs_ok`, so a module that imports one global twice is not covered.
- sym_prove has no `st_` rules yet for `local.tee`, `global.get`/`set`,
  `drop`, `select` and the loads and stores other than i32 (`step_rules`
  lists what it has); a `br` to a block with results is not handled.
- A call's spec in sym_prove is matched only when its P is `args == [...]
  && R(gs, ms, h)`; otherwise give it in `calls`. Loops containing calls
  are untested in sym_prove (`sl_loop_st_g` is proved; no example uses it).
- The evaluator computes on memory byte by byte, so it suits small memories.
  The spec cases that test the end of a 64 KiB page are not covered.
- The builder lacks `extend8_s`, `extend16_s` and `extend32_s`, so their spec
  cases are left out.
- WasmCert's soundness proofs (`Wasm_Properties`, `Wasm_Soundness`) are not
  ported. Nothing here depends on them.

### What the examples showed

About the rules' shapes:

- The instruction rules' "operands on top of some vs0" form does not glue
  by itself: each step needs an entailment. The exact-state `st_` rules
  and `norm` (state.mbt) made straight-line code glue with `sl_seq` alone,
  and sym_prove builds on them.
- `sl_br_if` and `sl_if` fix the condition, so the body is proved for
  each value and `sl_pure_l`, `sl_ex_l` put the invariant's facts and
  values back into the precondition.
- `sl_loop` and `sl_block` take their label assertions literally, so build
  the rule instance first and read the label from it (as sl_loop_st
  does) rather than writing it again.
- A comparison computes to `wasm_bool(word_ult(i, n))`; `wasm_bool_zero`
  turns `sl_br_if`'s and `sl_if`'s cases on it into the comparison itself.
- An invariant that names a fixed value of the specification (the array
  `xs` in `example_array_sum`) puts it in the loop's label too: do not
  rewrite or substitute it in a goal that still holds the labels.

About arrays and specs:

- The array rules by index (`st_arr_load_at`) on the whole array, with
  the array written as a right-nested APPEND and indices as sums of
  lengths (`val(i) == LENGTH(A) + LENGTH(L)`), let one lemma do each EL
  and list_update (`el_mid`, `part_swap` in the quicksort).
- Specs about a segment of a whole array (`A ++ B ++ Cs`, with lengths for
  lo and hi) need no heap splitting: the recursive calls choose A and Cs.
- `perm` by counts (equal FILTER lengths) needs no permutation library:
  each perm lemma is a case on one value and arithmetic. Arithmetic and
  list facts are best proved as lemmas first, so a condition's tactic only
  applies them.

About the automation (sym.mbt):

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
- Measured on straight-line code on the native target: 20 instructions in
  0.1 s, 100 in 0.6 s, so a long program is not the problem; loading is.

## Next steps

Done so far, in this order: more instructions, the automation, sorting,
calls (returns, recursion, calls in sym_prove), quicksort, the public API
and the adequacy theorems. Next, each mergeable on its own ("done when"
means the named theorems appear in `theory.md`, with the tests passing).
Reviewability comes before features, since every feature adds to what a
reviewer must read.

### Making the results reviewable

A proof trusts the kernel, the definition of `reduce` and the statement
proved, and nothing else, but the listings do not show which parts those
are. To trust `example_quicksort` by its definitions, a reviewer reads:

- the `wasm` definitions it rests on (the listing has 219 definitions and
  relations);
- the definitions behind `sl_triple_m`: `triple_l`, `safel`, `keep`,
  `lift`, `globs_ok`, `gvals`, `star`, `arr`, `words_bytes`, `pts`,
  `heap_of` and `mem_length`, spread among 448 lemmas that need no reading;
- a statement of 4,390 characters on one line, with both functions'
  bodies written out.

The adequacy theorems (`sl_triple_adequate`, `sl_triple_m_adequate`)
already state a triple's meaning with `reduce_trans` alone, so `safe`,
`safel`, `triple_l` and `keep` need no reading; `lift` and the heap
definitions still do. These steps shrink the rest to `reduce`, the
programs and a short statement about memory. The proofs are not part of
a review, because the kernel checks them, and the review document should
say so.

1. **Spec coverage of control flow.** Every example rests on the reduction
   rules for `block`, `loop`, `br`, `br_if`, `call` and `return`, and the
   spec tests check none of them (they cover `i32.wast`, `i64.wast` and
   loads from `address.wast`). Add the integer cases of `block.wast`,
   `loop.wast`, `br.wast`, `br_if.wast`, `call.wast` and `return.wast` that
   the evaluator covers (`tools/spec_cases.py`), and `br_table` and the
   `extend*_s` operators at the same time. Done when they hold as theorems
   in `wasm/spec_test.mbt`.

2. **Closed theorems for the examples.** For each example with memory or
   calls, a corollary about a store whose functions are the example's
   bodies and whose memory holds xs's bytes at p: every run of the call
   that ends, ends with the bytes at p being those of some ys that is
   sorted and a permutation of xs, with the other bytes unchanged. No
   assertion, heap or triple appears in the statement. `fact_closed` is
   done: `sl_triple_m_adequate_whole` (no frame, the whole memory j) with
   example_fact's R saying the globals and the memory are exactly the
   starting ones. Quicksort needs that R as `star(arr(val(p), xs),
   fp(gs, ms), h)`: fp the rest of the bytes, exactly, and a lemma that
   the bytes at p are `words_bytes(ys)` when the heap is. Done when
   `quicksort_closed` is in `theory.md`.

   These runs start from the code in a frame of the instance (`call 0`
   with a stack), not from a host's `Invoke` in `invoke_config`, whose
   frame is `empty_frame`. Covering that needs a lemma that an `Invoke`
   does not depend on the caller's frame (it pushes a frame of its own),
   since every triple here assumes `f_inst(f) == inst`.

3. **Named programs, readable statements.** Define each example's code as
   a constant (`qs_code`, `partition_code`, ...), so that statements name
   the program instead of writing it out; sym_prove then unfolds the name
   first. Print each code definition in the listing as WebAssembly text, so
   it can be compared with the pseudocode in the file's header. In the
   printer, abbreviate the type of a spec set as the other types are, and
   break long statements over several lines. Done when the examples'
   statements name their code and none is longer than 20 lines.

4. **A review document.** Generate `review.md` beside `theory.md`. For
   each closed theorem it shows the statement, then every definition the
   statement depends on (relations by their rules). The dependencies are
   found by following the statement's constants to their definitions,
   through `logic` and into `wasm`, stopping at hol_light's libraries. A
   line says that every other theorem is checked by the kernel and needs
   no reading. A snapshot test keeps the document current, as it does
   `theory.md`. Done when `review.md` covers every closed theorem.

5. **Non-vacuity checks.** A triple whose precondition nothing satisfies
   proves nothing, and several conjuncts could make one unsatisfiable
   without anyone noticing (`globs_ok`, `smem_ind` being `SOME`, `n_zeros`
   of the locals, the body's type). For each closed theorem, a test
   applies it to a concrete store built with `@wasm.store` and a small
   array, proves its hypotheses by computation, and checks that the
   evaluator's run (`@wasm.outcome`) gives a result the conclusion allows.
   Done when each closed theorem has such a test.

### Features

1. **`call_indirect`.** The target comes from a table in the store, which
   the triples do not fix (code without calls may write tables). Plan:
   keep the tables fixed in g triples as well as the functions, and carry
   over only call-free code with no table writes (a predicate like
   `call_free`, and its step lemma like `call_free_step`). Then
   `call_indirect` with the table's entry for c is `call` of that
   function, if its type is the one asked for. Done when a call through a
   function table is verified.

2. **Real programs.** An untrusted `.wat` or `.wasm` importer that makes
   programs through the builder, then verify a function from a compiled
   module (a sort from a C compiler is a good target: it adds a stack
   pointer global, its own stack frame in memory, and more instructions).
   The theorem is about the imported term, so the importer is trusted to
   match the file until someone verifies a decoder. This will want the
   missing `st_` rules (see "Known limits") and signed comparisons
   (`i32.lt_s`, `word_ilt`).

3. **One layer of triples (optional, for maintenance).** `safel` is `safer`
   with a return assertion that never holds, and `sl_triple_l` is close to
   `sl_triple_g` with no specs and no return. Restating the control rules
   once, for `sl_triple_g`, and deriving the `_l` ones would remove the
   copies in returns.mbt and specs.mbt (`safer_label` beside `label_safe`,
   `frame_safe_r` beside `frame_safe`, the `_g` block, loop and
   conditional rules) and half of sym's rules. The listing's statements
   would stay; the proofs move.

Not planned yet, with what they need:

- Functions of other modules: a spec's P and Q are about the caller's
  instance (its globals and memory), so a callee in another instance needs
  specs about that instance's state.
- Host functions are not provable as they are: WasmCert lets a host call
  trap in any state (`reduce` has a rule from any host invoke to
  `[Trap]`), so no triple of a host call holds. Covering them would mean
  assuming more about the host.
- A library of list lemmas (sorted, perm, EL and list_update through
  APPEND) instead of the ones each example proves for itself.

## Working on it

Build and test commands are in the README. After changing what a package defines
or proves, regenerate the listings and read the diff:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/logic --target wasm-gc --update
```

Add a new theorem you rely on to the list in `logic/logic_test.mbt`.
Generic tactics go in `tactics.mbt`; a helper only one proof uses stays
next to it. What is `pub` is the API the README describes: keep the two in
step.

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
- To see goals, add a whitebox test that sets `trace.val = true`
  (`@logic.set_trace(true)` from outside) and calls `load()`. `lemma` then
  names each lemma and prints the goals left over, and `show_goal("label")`
  inside a tactic prints the goal there. Remove the test afterwards.
- To work on one proof without reloading for each try, put it in a function
  that `load()` does not call, and call it from that test after `load()`:
  loading is most of a run's minute, and the proof then runs once more.
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
- `n_zeros` of a non-empty list needs `@ind_types.match_conv` (`those` is
  a `match`), after rewriting with its definitions.
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
- HOL constants named like variables: `F` (false), `I`, `K`, and
  constructors such as `U` (unsigned, of `Lt(U)`) cannot be variables; an
  `∃ U` binder is renamed `U'`.
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
