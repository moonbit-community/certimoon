// A port of WasmCert-Isabelle (https://github.com/WasmCert/WasmCert-Isabelle):
// the WebAssembly AST, numeric layer, typing and reduction relations
// (Wasm_Ast, Wasm_Type_Abs/Word, Wasm_Base_Defs, Wasm_Subtyping, Wasm).
// WasmCert-Isabelle is BSD-2-Clause, copyright its contributors.

///|
let loaded : Ref[Bool] = Ref::{ val: false }

///|
/// Load the WasmCert definitions (once), after Library/words.
pub fn load() -> Unit {
  if loaded.val {
    return
  }
  loaded.val = true
  @words.load()
  @parser.begin_theory("WasmCert")
  (fn() raise {
    define_helpers()
    define_ast()
    define_memory()
    define_int_ops()
    define_float_ops()
    define_conversions()
    define_mem_tab()
    define_values()
    define_app_ops()
    define_vec_ops()
    define_cvt()
    define_subtyping()
    define_store_lookups()
    define_extension()
    define_contexts()
    define_bounds()
    define_b_e_typing()
    define_store_typing_parts()
    define_e_typing()
    define_reduce_simple()
    define_reduce()
    define_reduce_trans()
  })() catch {
    e => abort("WasmCert: loading failed: " + e.to_string())
  }
  @parser.end_theory()
}
