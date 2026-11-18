// The theory as a document: every definition and lemma the package makes,
// in the order it makes them, with the kernel's statement of each.
// logic/logic_test.mbt keeps it in __snapshot__/theory.md.

///|
/// An entry of the listing: a definition, lemma or example, or a section
/// (with its title as `name` and no theorem); with the constants it
/// defines and where in the source it is made.
priv struct Entry {
  kind : String
  name : String
  th : @kernel.Thm?
  defines : Array[String]
  loc : String
}

///|
/// What `listing` shows, in order.
let entries : Array[Entry] = []

///|
/// A heading for the entries that follow.
pub fn section(title : String) -> Unit {
  if checking_proof() {
    return
  }
  entries.push({ kind: "section", name: title, th: None, defines: [], loc: "", })
}

///|
/// The logic's types, as the term syntax prints them (after the word
/// types are shortened), and short names for them, longest first.
let type_names : Array[(String, String)] = [
  (
    "(List[Value], List[Value], List[Value], Num, (Num) -> Option[Byte]) -> Bool",
    "SAssn",
  ),
  ("(List[Value], List[Value], Num, (Num) -> Option[Byte]) -> Bool", "FProp"),
  ("(Num, FProp, FProp) -> Bool", "Specs"),
  ("(List[Value], Num, (Num) -> Option[Byte]) -> Bool", "GProp"),
  ("(Wstore, Wframe, List[Value]) -> Bool", "Assn"),
  ("((Num) -> Option[Byte]) -> Bool", "HProp"),
  ("(Num) -> Option[Byte]", "Heap"),
  ("(Limit_t, List[Byte])", "Mem"),
  ("List[(Tab_t, List[V_ref])]", "Tabs"),
]

///|
/// `s` with the long types written by their short names.
fn abbreviate(s : String) -> String {
  let mut text = @wasm.abbreviate_types(s)
  for p in type_names {
    text = text.replace_all(old=p.0, new=p.1)
  }
  text
}

///|
/// `th`'s statement, laid out, with the long types written by their short
/// names.
fn statement(th : @kernel.Thm) -> @render.Statement raise {
  let t = @kernel.concl(th)
  @render.statement(
    t,
    abbreviate~,
    infixes=listing_infixes() + @wasm.word_infixes(t),
    atoms=@wasm.word_literals(t),
  )
}

///|
let infix_rules : Ref[Array[@render.Infix]?] = Ref::{ val: None, }

///|
fn listing_infixes() -> Array[@render.Infix] raise {
  if infix_rules.val is Some(rules) {
    return rules
  }
  let rules = [
    @render.Infix::new(
      @kernel.mk_const("star", @list.List([])),
      symbol="*",
      precedence=60,
      associativity=Right,
    ),
  ]
  infix_rules.val = Some(rules)
  rules
}

///|
/// An entry's statement as the listing shows it: a program's code in
/// WebAssembly's text format (`@wasm.wat_of_code`, which checks that the
/// text reads back as the code), anything else laid out.
fn entry_rendering(e : Entry) -> @render.Statement raise {
  match e.th {
    Some(th) if e.kind == "program" => {
      let (name, code) = @kernel.dest_eq(
        @basics.strip_forall(@kernel.concl(th)).1,
      )
      @render.Statement::plain(
        abbreviate(show(name)) + " ==\n" + @wasm.wat_of_code(code, indent="  "),
      )
    }
    Some(th) => statement(th)
    None => @render.Statement::plain("")
  }
}

///|
fn entry_statement(e : Entry) -> String raise {
  entry_rendering(e).text
}

///|
/// What package `logic` defines and proves, in order, as Markdown.
pub fn listing() -> String raise {
  load()
  listing_for(entries, "logic", "A separation logic for WasmCert")
}

///|
/// What package `logic` defines and proves, as data for a review site
/// (see `@render.export_entry`).
pub fn listing_json() -> String raise {
  load()
  json_for(entries, "logic", all_definitions())
}

///|
/// The entries of both packages that define constants, in listing order
/// (wasm's first): (package, name, constants defined, constants used).
fn all_definitions() -> Array[(String, String, Array[String], Array[String])] raise {
  let out = @wasm.definitions().map(d => ("wasm", d.0, d.1, d.2))
  for e in entries {
    if !e.defines.is_empty() && e.th is Some(th) {
      out.push(
        ("logic", e.name, e.defines, @render.term_constants(@kernel.concl(th))),
      )
    }
  }
  out
}

///|
/// What a statement using the constants `uses` depends on: the entries
/// that define them, and those that define the constants of those
/// entries' statements, and so on (package, name), in listing order; and
/// the constants left, which no entry of either package defines
/// (hol_light's), sorted.
pub fn depends_on(
  uses : Array[String],
) -> (Array[(String, String)], Array[String]) raise {
  load()
  @render.depends_on(uses, all_definitions())
}

///|
/// What each closed theorem depends on, as Markdown: every definition, by
/// package, and the constants of hol_light it uses; and for each example
/// (a triple), how many definitions. A change to what a theorem trusts
/// shows in this file's diff.
pub fn dependencies() -> String raise {
  load()
  dependencies_for(entries, "logic", all_definitions())
}

///|
fn listing_for(
  view : Array[Entry],
  pkg : String,
  title : String,
) -> String raise {
  let items = view.map(fn(e) raise { (e.kind, e.name, entry_statement(e)) })
  @render.render_listing(
    title,
    "What package `\{pkg}` defines and proves, in order, with the kernel's statement of each (every lemma is a theorem: loading the package proves it). Generated by `\{pkg}/\{pkg}_test.mbt`; run `moon test --update` to refresh it.\n\nTypes are abbreviated: `Byte`, `W32`, `W64` are words of 8, 32, 64 bits; `Heap` is `(Num) -> Option[Byte]` (what each address holds); `HProp` is a heap assertion `(Heap) -> Bool`; `Mem` is a WasmCert memory `(Limit_t, List[Byte])`; `Assn` is `(Wstore, Wframe, List[Value]) -> Bool` (an assertion on store, frame and value stack); `SAssn` is `(List[Value], List[Value], List[Value], Num, Heap) -> Bool` (on the value stack, the locals, the globals, the memory's length in bytes and the memory as a heap); `GProp` is `(List[Value], Num, Heap) -> Bool` (on the globals, the memory's length and the heap, the `R` of an exact state `st(v, l, R)`); `FProp` is `(List[Value], List[Value], Num, Heap) -> Bool` (on a list of values, the globals, the memory's length and the heap: a function's precondition or postcondition, on its arguments or results, or a loop's invariant, on the locals); `Specs` is `(Num, FProp, FProp) -> Bool` (a set of function specs: which function, its precondition and its postcondition); `Tabs` is `List[(Tab_t, List[V_ref])]` (a store's tables, each its type and its entries).\n\nA program (`program`) is a constant defined as a list of instructions; its entry shows the list in WebAssembly's text format, one instruction per line, printed from the kernel's definition and checked to read back as it (wasm/wat.mbt). An instruction it has no name for is written in the term syntax after `hol`.\n\n" +
    @render.layout_note,
    items,
  )
}

///|
fn json_for(
  view : Array[Entry],
  pkg : String,
  defs : Array[(String, String, Array[String], Array[String])],
) -> String raise {
  @render.render_json(
    pkg,
    view.map(fn(e) raise {
      let rendered = entry_rendering(e)
      let text = rendered.text
      let uses = match e.th {
        Some(th) => @render.term_constants(@kernel.concl(th))
        None => []
      }
      if e.kind == "theorem" || e.kind == "example" {
        let (deps, outside) = @render.depends_on(uses, defs)
        let depends = deps.map(d => d.0 + "/" + d.1)
        @render.export_entry(
          e.kind,
          e.name,
          text,
          uses,
          e.defines,
          e.loc,
          depends~,
          outside~,
          references=rendered.references,
          canonical=rendered.canonical,
        )
      } else {
        @render.export_entry(
          e.kind,
          e.name,
          text,
          uses,
          e.defines,
          e.loc,
          references=rendered.references,
          canonical=rendered.canonical,
        )
      }
    }),
  )
}

///|
fn dependencies_for(
  view : Array[Entry],
  pkg : String,
  defs : Array[(String, String, Array[String], Array[String])],
) -> String raise {
  let packages = ["wasm", "logic"] + (if pkg == "logic" { [] } else { [pkg] })
  let buf = StringBuilder()
  buf.write_string(
    "# What each theorem depends on\n\nTo trust a theorem, a reviewer reads its statement and the definitions it depends on: those defining the constants of its statement, and those defining the constants of theirs, through package logic and into package wasm, until only hol_light's constants are left. The proofs need no reading: the kernel checks them, and these packages add no axioms. Generated by `\{pkg}/\{pkg}_test.mbt`; run `moon test --update` to refresh it.\n",
  )
  let summary = (deps : Array[(String, String)]) => {
    "\{deps.length()} definitions: " +
    packages
    .map(p => "\{deps.filter(d => d.0 == p).length()} in \{p}")
    .join(", ")
  }
  for e in view {
    guard e.kind == "theorem" && e.th is Some(th) else { continue }
    let (deps, outside) = @render.depends_on(
      @render.term_constants(@kernel.concl(th)),
      defs,
    )
    buf.write_string("\n## Theorem `\{e.name}`\n\n\{summary(deps)}.\n")
    for pkg in ["logic", "wasm"] + (if pkg == "logic" { [] } else { [pkg] }) {
      let names = deps.filter(d => d.0 == pkg).map(d => d.1)
      buf.write_string(
        "\n### From \{pkg} (\{names.length()})\n\n```\n" +
        names.join("\n") +
        "\n```\n",
      )
    }
    buf.write_string(
      "\n### From hol_light (\{outside.length()} constants)\n\n```\n" +
      outside.join("\n") +
      "\n```\n",
    )
  }
  buf.write_string(
    "\n## Examples\n\nTriples of verified programs, with what their statements depend on.\n\n| Example | Definitions | " +
    packages.map(p => "In " + p).join(" | ") +
    " |\n|---|---|" +
    packages.map(_ => "---|").join("") +
    "\n",
  )
  for e in view {
    guard e.kind == "example" && e.th is Some(th) else { continue }
    let (deps, _) = @render.depends_on(
      @render.term_constants(@kernel.concl(th)),
      defs,
    )
    buf.write_string(
      "| `\{e.name}` | \{deps.length()} | " +
      packages
      .map(p => deps.filter(d => d.0 == p).length().to_string())
      .join(" | ") +
      " |\n",
    )
  }
  buf.to_string()
}
