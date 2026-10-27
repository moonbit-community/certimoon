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
`if`, `br`, `br_if`, `br_table`, `local.get/set/tee` and traps; these are
the builder's instructions. Floating point (left unspecified, as in
Isabelle), calls, globals, memory and tables are not covered: a term
written out with them raises "no rule for". `run` also takes a term built
any other way, when its instruction list and (for locals) frame are
written out. A `computes` theorem is about one run: Wasm reduction is
deterministic for this fragment, but the port does not prove that, so it
does not yet rule out a trapping run. `wasm/eval_test.mbt` has examples.

## Tests

`moon test` in a workspace tests every member, hol_light included, so
select the package. Its tests need a larger stack than the default:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/wasm --target wasm-gc
```
