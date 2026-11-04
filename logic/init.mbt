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
    section("Heaps and separating conjunction (heap.mbt)")
    define_heap()
    prove_heap()
    section("Loads and stores against points-to (memory.mbt)")
    prove_memory()
    prove_pts_split()
    section("Triples (triple.mbt)")
    define_triples()
    prove_triples()
    section("Sequencing (seq.mbt)")
    prove_sequencing()
    section("Lemmas for the instruction rules (rules.mbt)")
    prove_rule_lemmas()
    section("Triples with labels, br (labels.mbt)")
    define_labels()
    prove_labels()
    section("Steps of a label, blocks and loops (block.mbt, loop.mbt)")
    prove_label_steps()
    prove_br_facts()
    prove_label_safe()
    prove_block_rule()
    prove_loop_rule()
    section("More structural rules with labels (labels.mbt)")
    prove_label_extras()
    section("Instruction rules (rules.mbt)")
    prove_rules()
    section("Globals (globals.mbt)")
    prove_global_rules()
    section("Locals (locals.mbt)")
    prove_local_rules()
    section("Conditionals (conditionals.mbt)")
    prove_conditional_rules()
    section("Exact states (state.mbt)")
    prove_state_rules()
    section("Arrays (arrays.mbt)")
    prove_array_rules()
    section("Examples (examples.mbt)")
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
