///|
/// The logic's theory as a document: __snapshot__/theory.md.
test "the theory listing" (t : @test.Test) {
  t.write(@logic.listing())
  t.snapshot(filename="theory.md")
}
