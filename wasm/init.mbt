// A port of WasmCert-Isabelle (https://github.com/WasmCert/WasmCert-Isabelle):
// the WebAssembly AST, numeric layer, typing and reduction relations
// (Wasm_Ast, Wasm_Type_Abs/Word, Wasm_Base_Defs, Wasm_Subtyping, Wasm).
// WasmCert-Isabelle is BSD-2-Clause, copyright its contributors.

///|
let loaded : Ref[Bool] = Ref::{ val: false }

///|
/// Load the WasmCert definitions (once), after Library/words. It first
/// turns off hol_light's progress output: MESON's search depths
/// (`@lib.verbose`) and the parser's "inventing type variables" warning
/// (`@preterm.type_invention_warning`). Both only report, and the few
/// thousand proofs of a load printed pages of them. Set them back to true
/// after load() to see them.
pub fn load() -> Unit {
  if loaded.val {
    return
  }
  loaded.val = true
  @lib.verbose.val = false
  @preterm.type_invention_warning.val = false
  @words.load()
  @theory.begin_theory("WasmCert")
  (fn() raise {
    section("List and option helpers")
    define_helpers()
    section("Abstract syntax (Wasm_Ast)")
    define_ast()
    section("Bytes and memories")
    define_memory()
    section("Integer operations")
    define_int_ops()
    section("Floating point (unspecified)")
    define_float_ops()
    section("Conversions")
    define_conversions()
    section("Loads, stores, memories and tables")
    define_mem_tab()
    section("Values")
    define_values()
    section("Applying operators")
    define_app_ops()
    section("Vector operators")
    define_vec_ops()
    section("Numeric conversions")
    define_cvt()
    section("Subtyping")
    define_subtyping()
    section("Store and instance lookups")
    define_store_lookups()
    section("Store extension")
    define_extension()
    section("Evaluation contexts")
    define_contexts()
    section("Bounds")
    define_bounds()
    section("Typing of basic instructions")
    define_b_e_typing()
    section("Typing of stores")
    define_store_typing_parts()
    section("Typing of instructions")
    define_e_typing()
    section("Reduction without the store (reduce_simple)")
    define_reduce_simple()
    section("Reduction (reduce)")
    define_reduce()
    section("Runs (reduce_trans)")
    define_reduce_trans()
  })() catch {
    e => abort("certimoon/wasm: loading failed: " + e.to_string())
  }
  @theory.end_theory()
}
