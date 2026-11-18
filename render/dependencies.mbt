// Follow defining entries in any collection of HOL theories.

///|
/// Follow defining entries and return them in input order, plus sorted external
/// constants. Each input is (package, entry name, defined constants, used
/// constants). Cycles are visited once; the first definer of a constant wins.
pub fn depends_on(
  uses : Array[String],
  defs : Array[(String, String, Array[String], Array[String])],
) -> (Array[(String, String)], Array[String]) {
  let definer : Map[String, Int32] = Map([])
  for i, d in defs {
    for c in d.2 {
      if !definer.contains(c) {
        definer[c] = i
      }
    }
  }
  let need : Set[Int32] = Set([])
  let outside : Set[String] = Set([])
  let todo = uses.copy()
  while todo.pop() is Some(c) {
    match definer.get(c) {
      None => outside.add(c)
      Some(i) =>
        if !need.contains(i) {
          need.add(i)
          for u in defs[i].3 {
            todo.push(u)
          }
        }
    }
  }
  let deps = []
  for i, d in defs {
    if need.contains(i) {
      deps.push((d.0, d.1))
    }
  }
  let rest = outside.iter().collect()
  rest.sort()
  (deps, rest)
}
