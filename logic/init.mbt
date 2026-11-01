// A separation logic for WebAssembly programs on linear memory, on top of
// package wasm's semantics (the WasmCert-Isabelle port). Every rule is a
// theorem proved from the reduction relation; nothing is assumed.

///|
let loaded : Ref[Bool] = Ref::{ val: false }

///|
/// Load the logic's definitions and lemmas (once), after package wasm's
/// definitions.
pub fn load() -> Unit {
  if loaded.val {
    return
  }
  loaded.val = true
  @wasm.load()
  @parser.begin_theory("WasmLogic")
  (fn() raise {
    define_heap()
    prove_heap()
    prove_memory()
  })() catch {
    e => {
      let msg = match e {
        Failure(m) => m
        _ => e.to_string()
      }
      // abort's message does not reach the test output on every target
      println("wasmcert/logic: loading failed: " + msg)
      abort("wasmcert/logic: loading failed: " + msg)
    }
  }
  @parser.end_theory()
}
