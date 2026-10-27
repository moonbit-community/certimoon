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
values) or `traps`:

```moonbit
let cfg = @term_syntax.parse_term(
  "((s : Wstore), Wframe(NIL, (i : Inst)), [Basic(EConstNum(ConstInt32(word(10)))), Basic(EConstNum(ConstInt32(word(2)))), Basic(Binop(T_i32, Binop_i(Div(S))))])",
)
@wasm.outcome(cfg)
// ⊢ computes(cfg, s, [V_num(ConstInt32(word(5)))])
```

It covers numeric instructions, `ref.null`/`ref.is_null`, `unreachable`,
`nop`, `drop`, `select`, `block`, `loop`, `if`, `br`, `br_if`, `br_table`,
`local.get/set/tee` and traps; calls, globals, memory and tables raise "no
rule for". The instruction list must be written out, and the locals too
when the program uses them (`Wframe([...], inst)`); the store and instance
can stay variables. A `computes` theorem is about one run: Wasm reduction
is deterministic for this fragment, but the port does not prove that, so
it does not yet rule out a trapping run. `wasm/eval_test.mbt` has examples.

## Tests

`moon test` in a workspace tests every member, hol_light included, so
select the package. Its tests need a larger stack than the default:

```bash
ulimit -s 65520 && moon test -p moonbit-community/wasmcert/wasm --target wasm-gc
```
