// Compatibility entry point with Wasm's word type abbreviations.

///|
pub fn layout_statement(
  t : @kernel.Term,
  abbreviate~ : (String) -> String = abbreviate_types,
) -> String {
  @render.layout_statement(t, abbreviate~)
}
