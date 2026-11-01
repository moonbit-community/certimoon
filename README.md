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
rewrites its `pkg.generated.mbti` files. Check this module's package
alone, which keeps its own interface file current:

```bash
moon check wasm
```

## Status

Package `wasm` has the definitions of Wasm_Ast, Wasm_Type_Abs/Word,
Wasm_Base_Defs, Wasm_Subtyping and Wasm.thy: the WebAssembly AST, the
numeric layer (on Library/words), and the typing and reduction relations.
The header comments of `wasm/*.mbt` list where names and representations
differ from Isabelle's. The soundness proofs (Wasm_Properties,
Wasm_Soundness) are not ported yet.

```moonbit
@wasm.load()
let rules = @wasm.thm("reduce_rules") // also b_e_typing_rules, typeof_num, ...
```

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
  `n + off`, the functions the load and store reduction rules use.

Triples over the reduction relation and the rules for instructions are the
next step (not done yet).

## Tests

`moon test` in a workspace tests every member, hol_light included, so
select the package. Its tests need a larger stack than the default:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/wasm --target wasm-gc
```

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/logic --target wasm-gc
```
