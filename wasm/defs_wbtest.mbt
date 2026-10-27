///|
test "datatype rejects an unknown type name" {
  // `Nmu` is not a type, so the term syntax reads it as a type variable;
  // the check fails before anything is defined
  let msg = try {
    datatype("zz_typo", [("Zz_typo", ["Nmu"])])
    ""
  } catch {
    Failure(m) => m
    e => e.to_string()
  }
  assert_true(msg.contains("unknown type in Nmu"), msg~)
}
