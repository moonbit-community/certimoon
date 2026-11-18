# TLSF individual proof checks

Originally implemented on `codex/tlsf-lemma-checks` at CertiMoon
`4b57c7d02866abf96065dba133b08b40a0cb5da3`, then integrated with
`53180c7` and its page-publication, `try_malloc`, and `full_malloc` proofs,
including memory growth and retry. The HOL dependency is
`da8dc488abaae7638eb300879e9cb30711e0dc8d`.

## Running the modes

```sh
ulimit -s 65520
moon run cmd/tlsf --target wasm-gc -- check tlsf_find_sound
moon run cmd/tlsf --target wasm-gc -- check tlsf_try_malloc_run tlsf_full_malloc_run
moon run cmd/tlsf --target wasm-gc -- check --all
moon run cmd/tlsf --target wasm-gc -- check --keep-going NAME1 NAME2
moon run cmd/tlsf --target wasm-gc -- list
moon run cmd/tlsf --target wasm-gc -- verify
```

`check NAME` builds the declaration prefix ending at NAME, then executes that
proof body. Multiple names share the complete declaration catalog. Each check
can use only declarations preceding its own position. Results are not cached:
checking a name again executes its proof again. Sharing setup currently applies
to checks within the same executable process; recompiling after a source edit
starts a new process and loads the checked base again.

`--keep-going` reports every selected proof independently, including failures,
and exits nonzero if any check fails. Each check restores its scoped context;
failed or conditional results do not enter the verified registry. This lets
independent proof fixes share one declaration setup.

The API equivalents are `@tlsf.check_lemma(name)`,
`@tlsf.prepare_checks().check(name)`, and `@tlsf.verify()`.

## What a successful check establishes

Earlier TLSF lemmas are supplied by the kernel's assumption rule, as explicit
hypotheses. A selected proof must return its declared conclusion, with every
remaining hypothesis an instance of an earlier lemma statement. Self and
forward lookups are rejected. The returned `LemmaCheck.theorem()` discharges
the actual hypotheses into a closed implication; it does not return the
selected conclusion as an unconditional theorem.

Conditional declarations and results stay outside the normal theorem registry
and listings. No kernel change, axiom, trusted theorem deserialization, or
unchecked theorem constructor was added. Both command modes run the existing
upstream axiom audit. Full replay runs the same proof builders with proved
predecessors and requires every TLSF definition/program/lemma/example to have no
hypotheses.

HOL, WasmCert definitions/properties, and the core logic remain fully replayed
in this first implementation. TLSF definitions are also constructed through
the kernel. Declaration setup still evaluates shared term/tactic construction
and a few unnamed helper derivations. It skips every registered TLSF proof
body. These remaining setup costs are included in the cold measurements.

Kernel definitions cannot be rolled back. Full TLSF replay after conditional
setup requires a fresh process, including after failed preparation. A partial
catalog can check its predecessors again, but cannot extend to later
declarations in the same process.

## Implementation notes

- TLSF's statement declarations retain lazy tactic/VC builders. The statement
  is parsed once and its `Term` is retained by the builder, preserving inferred
  type variables even when proof execution happens much later.
- Scoped helpers in `logic/proof_check.mbt` collect declarations, limit theorem
  lookup to earlier positions, check conclusions/premises, and keep conditional
  results private. Ordinary `prove` remains strict outside that scope.
- HOL's `PART_MATCH` rejects changes to hypotheses during matching. Conditional
  polymorphic rewrite premises are therefore explicitly type-instantiated
  before use, using types appearing in the available declaration prefix.
  Matching modus ponens specializes against its actual goal. The resulting
  hypotheses are still checked against earlier schemas at the boundary.
- The initialization zero-suffix proof now reads its arithmetic condition
  from the implication's antecedent. Its former `hypotheses[0]` lookup selected
  a lemma premise when conditional checking added hypotheses.
- Source locations in the JSON snapshot were refreshed. Statements, kinds,
  defined constants, and dependency data are unchanged. The existing stale
  core location for `example_false_ordinary_continuation` had already been
  corrected in the malloc work. The Markdown and dependency snapshots are
  unchanged by integration.
- Integration preserves the core `sl_or_g` rule and nonrecursive
  `@drule.new_definition` program construction, which avoids deep recursive
  definition processing for the long compiled malloc bodies.
- Ordinary `@logic.def` equations now also use `@drule.new_definition` when
  the head is fresh, the parameters are distinct variables, and the right
  side contains neither recursion nor hidden free term/type variables.
  Recursive and pattern definitions, existing constants, and other forms
  retain `@define.define_`. The wrapper restores the general processor's
  explicit quantifiers and definition registry, including benign redefinition.
  This changes definition construction, with no new axiom or trusted rule.

## Measurements before malloc integration

These measurements cover the original 754-proof worktree at `4b57c7d`,
not the larger allocator now present in this checkout.

Measured on macOS 26.6.2 arm64, **wasm-gc debug**, using Moon/moonrun
`0.1.20261113` and `moonc v0.10.21+d1f75be79-nightly`. One fresh-process
run per workload; these are observed timings, not a variance estimate.

| Workload | Process wall | Checked base | TLSF setup/replay | Selected proof | Speedup |
|---|---:|---:|---:|---:|---:|
| Full verification | 209.811 s | 67.665 s | 130.226 s | included | 1.00x |
| `tlsf_exp_le` | 76.604 s | 64.705 s | 0.067 s | 0.241 ms | 2.74x |
| `tlsf_find_sound` | 104.258 s | 67.545 s | 0.113 s | 24.828 s | 2.01x |
| `tlsf_block_free_all` | 115.621 s | 68.178 s | 35.812 s | 5.554 ms | 1.81x |

The early lemma is **2.74x faster**, the expensive search lemma **2.01x**,
and the final theorem **1.81x**. The remaining 65–68 seconds of checked-base
loading limit cold-process speedups. Selecting an early lemma also avoids
constructing later TLSF definitions. Reusing a prepared plan avoids repeating
base and declaration setup.

Full verification reported **988 closed named declarations and three approved
axioms**. The native backend passed compilation; native release and wasm-gc
release were not timed in this comparison.

Raw results: [cold-process benchmark](benchmarks/tlsf-checks-wasm-gc-debug-2026-11-17.json)
and [validation summary](benchmarks/tlsf-validation-2026-11-17.json).

The benchmark builds once, then runs fresh processes sequentially with the same
executable. Process wall time includes runtime startup and excludes compilation.
Phase timers use MoonBit's monotonic clock. The comparison is full proof replay
versus one conditional proof; the 20-test execution/snapshot suite is a separate
workload.

```sh
ulimit -s 65520
python3 tools/benchmark_tlsf_checks.py --repeat 1 \
  --out tools/benchmarks/tlsf-checks-wasm-gc-debug-2026-11-17.json
```

Use `--repeat 2` for repeated cold samples, `--release` for release mode, or
`--target native --release` for native release. Timings from one backend/mode
must not be presented as measurements of another.

## Original worktree validation

- All 754 TLSF lemma/example proofs checked individually against earlier
  statements, with the upstream axiom audit after every result.
- Existing TLSF suite: 20 tests passed, including full replay, closed-theorem
  checks, concrete allocator executions, and snapshots.
- Core logic suite: 20 tests passed, including eight checker regression tests
  for laziness, reuse, isolation, self/future/unrelated premises, polymorphic
  instantiation, failure cleanup, inferred types, and strict full replay.
- Native package checks passed; runtime speed measurements below are explicitly
  labeled by backend and build mode.
- Python tool suite: 26 passed, five skipped because the optional executable
  fixtures are not present in this worktree. The benchmark driver is exercised
  by the recorded measurements.

The existing Markdown theory and dependency snapshots remain unchanged.

## Integration with malloc proofs

Integration at `53180c7` checks all **979** TLSF lemma/example proofs
individually. This includes page publication, both compiled allocation entry
points, memory growth, retry, and the closed run theorems. The checked base
remains fully replayed, and the same core checker regression suite passes.

A fresh `check tlsf_full_malloc_run` passed in **148.4 s** process wall time:
67.84 s for the checked base, 68.90 s for TLSF declarations, and 10.52 ms for
the selected proof. This was an integration validation run with other tests
and performance investigation potentially overlapping, not a sequential
benchmark or a new speedup estimate. The original timings above remain the
comparison for the older allocator.

Integration validation passes all 979 individual proofs, 23 allocator tests
(including full replay, all closed named theorems, concrete executions, and
all three snapshots), 20 core/checker tests, 38 Python tests, and 21 shipped-WAT
comparisons. Native package checking also passes. There are no new axioms, and
theorem statements and dependency snapshots are unchanged.

Raw results: [integration validation](benchmarks/tlsf-checks-integration-2026-11-17.json).

## Public free verification

The public-free extension adds 41 independently checked lemmas, bringing the
allocator to 1,333 closed named declarations. Full replay, all 24 allocator
tests and their snapshots, 42 Python tests, and 22 shipped-WAT comparisons
pass. The compiled public function has 199 instructions. Validation covers
complete native guarded exits in the kernel and both live-allocation paths
with full-memory comparisons in a real Wasm engine.

Raw results: [public-free validation](benchmarks/tlsf-public-free-validation-2026-11-17.json).

## Nonrecursive definition setup

This comparison uses the current public-free proofs at baseline `c5ea1f5`,
with only the ordinary-definition fast path changed in the candidate.
Both retain direct kernel construction of program definitions. Measurements
use frozen **wasm-gc debug** executables, fresh sequential processes, and
exclude compilation. The late conditional check is `tlsf_public_free_run`:
two samples per variant, in baseline/candidate then candidate/baseline order.
Full verification has one separate sample per variant.

| Metric | Baseline | Fast path | Speedup |
|---|---:|---:|---:|
| Checked base, median | 61.131 s | 61.046 s | 1.00x |
| TLSF declarations, median | 63.721 s | 19.851 s | 3.21x |
| Late conditional check, process wall median | 135.659 s | 91.740 s | 1.48x |
| Full verification, process wall (one sample each) | 251.803 s | 209.365 s | 1.20x |

The cold check saves **43.9 seconds**. Checked-base loading remains the
largest part of its runtime after the change. Full replay saves **42.4 seconds**;
both variants verified **1,333 closed named declarations and three approved
axioms**.

The benchmark also requires identical conditional results/premises and
identical full-replay declaration/axiom audits. This is a setup optimization;
the checked base and selected proof still run normally.

Four new white-box regressions cover eligibility/fallback guards, theorem
shape against the general processor (including polymorphism and partial or
reordered quantifiers), benign redefinition, and execution of a recursive
pattern definition. All 24 core tests and all 24 allocator tests pass, including
strict full replay, concrete executions, and unchanged snapshots. Native
package checking, 42 Python tests, and 22 shipped-WAT comparisons also pass.
The public interfaces are unchanged.

To reproduce, run `moon build cmd/tlsf --target wasm-gc` in baseline and candidate
checkouts with the same toolchain. Copy each reported executable to a separate
path before rebuilding, then run:

```sh
python3 tools/benchmark_definition_setup.py \
  --baseline /tmp/tlsf-before.wasm --candidate /tmp/tlsf-after.wasm \
  --baseline-revision c5ea1f5 --repeat 2 --verify-repeat 1 \
  --out /tmp/nonrecursive-definitions.json
```

Artifact hashes, toolchain versions, stack limits, phase timings, and raw
result events are retained in the JSON report. These sample counts describe
observed local performance, without a statistical confidence interval or
claims about native/release builds.

Raw results: [nonrecursive-definition benchmark](benchmarks/nonrecursive-definitions-wasm-gc-debug-2026-11-17.json).

## Lazy allocation startup

The startup extension adds 96 named declarations, bringing the allocator to
1,429. Strict kernel replay checks every declaration and retains the same
three approved axioms. The closed call and execution theorems are
`tlsf_try_malloc_start_all`, `tlsf_full_malloc_start_all`,
`tlsf_try_malloc_start_run`, and `tlsf_full_malloc_start_run`.

The proofs cover the zero request, both initialization-guard paths, native
initialization with or without growth, initialization failure before any write,
no-fit after successful initialization, and full_malloc's further growth,
retry, and failure. The startup heap owns a zeroed unused suffix and an
arbitrary disjoint client frame, kept at its original memory length on every
outcome. Return-aware abort composition rules are proved in the allocator
package and discharged from the exported execution theorems.

The Python suite passes all 49 tests, including seven startup runtime tests
with multiple fixtures. These run the compiler's WAT with bounded memories,
check free-memory membership and size classes, and retain client canaries
through subsequent allocation and free. Fixtures include zero-page memory,
an initialization-guard slot outside memory, an arena too small for the first
request, the maximum supported request, and successful initial growth followed
by failed allocation growth. All 22 shipped-WAT comparisons pass.

All 25 allocator tests pass, including strict replay, concrete native-closure
premises for the new contracts, and the three snapshot checks. The theory's
Markdown and JSON snapshots are updated; the example-only dependency summary
is unchanged. A snapshot audit confirms that all 1,333 previous statements,
kinds, uses, and definitions are unchanged. Wasm-GC and native package checking
pass, and the public interfaces are unchanged.

Raw results: [lazy-startup validation](benchmarks/tlsf-lazy-startup-validation-2026-11-18.json).
