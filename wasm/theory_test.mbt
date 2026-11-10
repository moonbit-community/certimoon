///|
/// The package's theory as a document: __snapshot__/theory.md.
test "the theory listing" (t : @test.Test) {
  t.write(@wasm.listing())
  t.snapshot(filename="theory.md")
}

///|
/// The same as data, for the review site (tools/review_site.py):
/// __snapshot__/theory.json.
test "the theory as data" (t : @test.Test) {
  t.write(@wasm.listing_json())
  t.snapshot(filename="theory.json")
}
