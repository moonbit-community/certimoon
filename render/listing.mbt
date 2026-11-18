///|
/// The listing in Markdown: `items` are (kind, name, statement), and a
/// ("section", title, _) is a heading for the items after it.
pub fn render_listing(
  title : String,
  intro : String,
  items : Array[(String, String, String)],
) -> String {
  let buf = StringBuilder()
  buf.write_string("# " + title + "\n\n" + intro + "\n")
  for e in items {
    let (kind, name, text) = e
    if kind == "section" {
      buf.write_string("\n## " + name + "\n")
    } else {
      buf.write_string(
        "\n" + kind + " `" + name + "`\n\n```\n" + text + "\n```\n",
      )
    }
  }
  buf.to_string()
}

///|
/// How the listings lay statements out, for their introductions.
pub let layout_note : String = "A statement is laid out as `∀ (x y : T) (z : U)`, its variables grouped by type; then, if it has hypotheses, `if` and the numbered hypotheses H1, ..., Hn and `then` and the conclusion C, with `or` between alternatives and `&&` before each further conjunct (as between a definition's equations). It stands for `∀ x y z, H1 && ... && Hn → C`. A line longer than 80 characters is broken by its brackets and operators, an argument, conjunct or case per line; only whitespace changes. Each layout is printed from the kernel's statement and checked to read back as it (wasm/layout.mbt)."
