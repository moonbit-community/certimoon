// A separation logic for WebAssembly programs on linear memory, on top of
// package wasm's semantics (the WasmCert-Isabelle port). Every rule is a
// theorem proved from the reduction relation; nothing is assumed.

///|
let loaded : Ref[Bool] = Ref::{ val: false }

///|
/// Load the logic's definitions and lemmas (once), after package wasm's
/// facts about reduction.
pub fn load() -> Unit {
  if loaded.val {
    return
  }
  loaded.val = true
  @wasm.props() catch {
    e => abort("wasmcert/logic: " + e.to_string())
  }
  @parser.begin_theory("WasmLogic")
  (fn() raise {
    define_heap()
    prove_heap()
    prove_memory()
    define_triples()
    prove_triples()
    prove_sequencing()
    prove_rule_lemmas()
    define_labels()
    prove_labels()
    prove_label_steps()
    prove_br_facts()
    prove_label_safe()
    prove_block_rule()
    prove_loop_rule()
    prove_rules()
    prove_examples()
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
