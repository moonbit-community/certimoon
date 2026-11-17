// A client package can replay proofs with the same logic tactics while
// keeping its loading and review snapshots separate from the core theory.

///|
struct Extension {
  pkg : String
  title : String
  entries : Array[Entry]
}

///|
/// Replay a client theory and capture its listing. The kernel and named
/// theorem/program registries are shared, so existing proof tactics work
/// across packages. Core listings stay independent of loaded extensions.
/// Like loading the core theory, a failed replay cannot roll back the kernel.
pub fn extend_theory(
  pkg : String,
  build : () -> Unit raise,
  title~ : String = pkg,
) -> Extension raise {
  load()
  if in_load.val || checking_proof() {
    raise Failure("cannot nest a theory extension")
  }
  let start = entries.length()
  @theory.begin_theory(pkg)
  in_load.val = true
  defer {
    in_load.val = false
    while entries.length() > start {
      ignore(entries.pop())
    }
    @theory.end_theory()
  }
  build()
  { pkg, title, entries: entries[start:].to_owned(), }
}

///|
pub fn Extension::names(self : Extension) -> Array[String] {
  self.entries.filter(e => e.th is Some(_)).map(e => e.name)
}

///|
pub fn Extension::listing(self : Extension) -> String raise {
  listing_for(self.entries, self.pkg, self.title)
}

///|
fn Extension::definitions(
  self : Extension,
) -> Array[(String, String, Array[String], Array[String])] raise {
  let out = all_definitions()
  for e in self.entries {
    if !e.defines.is_empty() && e.th is Some(th) {
      out.push(
        (self.pkg, e.name, e.defines, @wasm.term_constants(@kernel.concl(th))),
      )
    }
  }
  out
}

///|
pub fn Extension::listing_json(self : Extension) -> String raise {
  json_for(self.entries, self.pkg, self.definitions())
}

///|
pub fn Extension::dependencies(self : Extension) -> String raise {
  dependencies_for(self.entries, self.pkg, self.definitions())
}
