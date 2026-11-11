#!/usr/bin/env python3
"""Writes a static site for reviewing what packages wasm and logic define
and prove, from their listings as data (wasm/__snapshot__/theory.json and
logic/__snapshot__/theory.json, kept by the packages' tests):

    python3 tools/review_site.py [--out _site] [--source-url URL]

- index.html: the closed theorems in full, with what each depends on,
  then the examples and the source files;
- <package>/<file>.html for each source file: its entries in order under
  the listing's headings, definitions in full and lemmas folded;
- review/<name>.html for each closed theorem and example: its statement,
  the programs it is about, then every other definition it depends on,
  with links to entries on the page staying on it. Package logic computes that list
  (`depends` in its theory.json, also kept in
  logic/__snapshot__/dependencies.md): the entries defining the constants
  of the statement, and those defining the constants of theirs, through
  logic and into wasm, until only hol_light's constants are left.

Every statement is the listing's text, as the kernel's statement printed
by the packages; this script only links its constants to the entries that
define them, and lays out the pages. `--source-url` is where a source
link goes: the file's path and `#L<line>` are appended (by default the
repository on GitHub at main).
"""

import argparse
import html
import json
import os
import re
import sys

PACKAGES = ["wasm", "logic"]
DEFINING = {"definition", "relation", "datatype", "record", "constant",
            "type definition", "specification", "program"}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

CSS = """
/* a reference manual: a file tree on the left, entries on the right */
:root {
  --bg: #ffffff; --fg: #1c1d22; --muted: #686b78; --line: #e2e3ea;
  --panel: #f5f6f9; --accent: #1f56c7; --code: #fafbfd;
  --def: #17703f; --rel: #8a4b00; --lem: #686b78; --ex: #9b1d73;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #141519; --fg: #e9eaf0; --muted: #9a9caa; --line: #2b2d35;
    --panel: #1b1c22; --accent: #8db0f7; --code: #18191e;
    --def: #63cf8f; --rel: #eda65c; --lem: #9a9caa; --ex: #ee82cf;
    color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --bg: #141519; --fg: #e9eaf0; --muted: #9a9caa; --line: #2b2d35;
  --panel: #1b1c22; --accent: #8db0f7; --code: #18191e;
  --def: #63cf8f; --rel: #eda65c; --lem: #9a9caa; --ex: #ee82cf;
  color-scheme: dark;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--fg);
  font: 15px/1.5 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
.layout { display: flex; min-height: 100vh; }
nav { width: 260px; flex: none; border-right: 1px solid var(--line);
  background: var(--panel); padding: 16px; position: sticky; top: 0;
  height: 100vh; overflow-y: auto; font-size: 14px; }
nav h2 { font-size: 12px; text-transform: uppercase; letter-spacing: .05em;
  color: var(--muted); margin: 16px 0 4px; }
nav ul { list-style: none; margin: 0; padding: 0; }
nav li a { display: block; padding: 2px 6px; border-radius: 4px; }
nav li a.here { background: var(--line); }
nav input { width: 100%; padding: 6px 8px; border: 1px solid var(--line);
  border-radius: 6px; background: var(--bg); color: var(--fg); }
#results { margin-top: 6px; }
main { flex: 1; min-width: 0; padding-block: 24px 64px;
  padding-left: max(32px, env(safe-area-inset-left, 0px));
  padding-right: max(32px, env(safe-area-inset-right, 0px)); max-width: 1100px; }
h1 { font-size: 24px; margin: 0 0 8px; }
h2.section { font-size: 18px; margin: 32px 0 8px; padding-bottom: 4px;
  border-bottom: 1px solid var(--line); }
.entry { margin: 14px 0; }
.head { display: flex; gap: 8px; align-items: baseline; flex-wrap: wrap; }
.kind { font-size: 12px; font-weight: 600; text-transform: uppercase;
  letter-spacing: .04em; }
.k-definition, .k-datatype, .k-record, .k-constant, .k-type-definition,
.k-specification { color: var(--def); }
.k-program { color: var(--ex); }
.k-relation { color: var(--rel); }
.k-lemma { color: var(--lem); }
.k-example, .k-theorem { color: var(--ex); }
.name { font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-weight: 600; }
.src { font-size: 12px; color: var(--muted); }
pre { background: var(--code); border: 1px solid var(--line);
  border-radius: 6px; padding: 10px 12px; margin: 6px 0; overflow-x: auto;
  font: 13px/1.45 ui-monospace, SFMono-Regular, Menlo, monospace; }
details > summary { cursor: pointer; }
details.lemma > summary { list-style: none; }
details.lemma > summary::-webkit-details-marker { display: none; }
details.lemma > summary::before { content: "▸ "; color: var(--muted); }
details.lemma[open] > summary::before { content: "▾ "; }
.usedby { font-size: 13px; color: var(--muted); }
.note { background: var(--panel); border: 1px solid var(--line);
  border-radius: 8px; padding: 12px 16px; margin: 12px 0; }
table { border-collapse: collapse; margin: 8px 0; }
td, th { text-align: left; padding: 4px 12px 4px 0;
  border-bottom: 1px solid var(--line); font-size: 14px; }
th { color: var(--muted); font-weight: 600; }
.muted { color: var(--muted); }
code { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 13px; }
@media (max-width: 760px) {
  .layout { display: block; }
  nav { width: auto; height: auto; position: static; border-right: none;
    border-bottom: 1px solid var(--line); }
  main { padding-left: max(16px, env(safe-area-inset-left, 0px));
    padding-right: max(16px, env(safe-area-inset-right, 0px)); }
  nav { padding-left: max(16px, env(safe-area-inset-left, 0px));
    padding-right: max(16px, env(safe-area-inset-right, 0px)); }
}
"""

SEARCH_JS = """
(function () {
  var box = document.getElementById('search');
  var out = document.getElementById('results');
  if (!box) return;
  box.addEventListener('input', function () {
    var q = box.value.trim().toLowerCase();
    out.innerHTML = '';
    if (q.length < 2) return;
    var n = 0;
    for (var i = 0; i < SEARCH.length && n < 30; i++) {
      var e = SEARCH[i];
      if (e[0].toLowerCase().indexOf(q) >= 0) {
        var li = document.createElement('li');
        var a = document.createElement('a');
        a.href = ROOT + e[1];
        a.textContent = e[0];
        li.appendChild(a);
        out.appendChild(li);
        n++;
      }
    }
  });
})();
"""


def esc(s):
    return html.escape(s, quote=True)


def anchor(name):
    return "e-" + re.sub(r"[^A-Za-z0-9_-]", lambda m: "_%02x" % ord(m.group(0)), name)


class Site:
    def __init__(self, root, source_url):
        self.source_url = source_url.rstrip("/") + "/"
        self.entries = []      # all entries but sections, in order
        self.by_name = {}
        self.by_key = {}       # "package/name" -> entry
        self.definer = {}      # constant -> entry
        for pkg in PACKAGES:
            path = os.path.join(root, pkg, "__snapshot__", "theory.json")
            data = json.load(open(path))
            section = ""
            for e in data["entries"]:
                if e["kind"] == "section":
                    section = e["name"]
                    continue
                e["package"] = pkg
                e["section"] = section
                if not e["file"]:
                    e["file"] = pkg + "/unknown.mbt"
                e["page"] = page_of(e["file"])
                self.entries.append(e)
                self.by_name.setdefault(e["name"], e)
                self.by_key[pkg + "/" + e["name"]] = e
                for c in e["defines"]:
                    self.definer.setdefault(c, e)
        # used by: entries whose statements use a constant this one defines
        self.used_by = {}
        for e in self.entries:
            for c in e["uses"]:
                d = self.definer.get(c)
                if d is not None and d is not e:
                    self.used_by.setdefault(id(d), []).append(e)
        self.pages = []        # (package, file, page) in order of first entry
        seen = set()
        for e in self.entries:
            if e["page"] not in seen:
                seen.add(e["page"])
                self.pages.append((e["package"], e["file"], e["page"]))
        # closed theorems (about runs, with no assertion) first, then the
        # examples (triples): each has a review page
        self.theorems = [e for e in self.entries if e["kind"] == "theorem"]
        self.examples = [e for e in self.entries if e["kind"] == "example"]
        self.reviewed = self.theorems + self.examples

    def href(self, e, depth, here=()):
        """A link to entry `e`: within this page when `e` is on it (`here`
        holds the ids of the entries on a review page), else to its file's page."""
        if id(e) in here:
            return "#" + anchor(e["name"])
        return "../" * depth + e["page"] + "#" + anchor(e["name"])

    def linked(self, e, depth, here=()):
        """The statement of `e` with the constants it uses linked to the
        entries that define them."""
        text = e["statement"]
        uses = set(e["uses"])
        out, k = [], 0
        for m in IDENT.finditer(text):
            name = m.group(0)
            out.append(esc(text[k:m.start()]))
            d = self.definer.get(name) if name in uses else None
            if d is not None and d is not e:
                out.append(f'<a href="{self.href(d, depth, here)}" title="{esc(d["kind"])} {esc(d["name"])}">{esc(name)}</a>')
            else:
                out.append(esc(name))
            k = m.end()
        out.append(esc(text[k:]))
        return "".join(out)

    def source_link(self, e):
        if not e["line"]:
            return ""
        return (f'<a class="src" href="{esc(self.source_url + e["file"])}#L{e["line"]}">'
                f'{esc(e["file"])}:{e["line"]}</a>')

    def entry_html(self, e, depth, fold_lemmas=True, here=()):
        kind_cls = "k-" + e["kind"].replace(" ", "-")
        head = (f'<span class="kind {kind_cls}">{esc(e["kind"])}</span> '
                f'<span class="name">{esc(e["name"])}</span> {self.source_link(e)}')
        body = f'<pre>{self.linked(e, depth, here)}</pre>' if e["statement"] else ""
        users = self.used_by.get(id(e), [])
        if users:
            links = ", ".join(f'<a href="{self.href(u, depth, here)}">{esc(u["name"])}</a>' for u in users[:60])
            more = f" and {len(users) - 60} more" if len(users) > 60 else ""
            body += (f'<details class="usedby"><summary>used by {len(users)}</summary>'
                     f'{links}{more}</details>')
        # (the review page shows its theorem unfolded, and is that page)
        if e["kind"] in ("theorem", "example") and fold_lemmas:
            body += (f'<div class="usedby"><a href="{"../" * depth}review/{esc(e["name"])}.html">'
                     f'what this depends on</a></div>')
        aid = anchor(e["name"])
        if fold_lemmas and e["kind"] == "lemma":
            return (f'<details class="entry lemma" id="{aid}"><summary class="head">{head}</summary>'
                    f'{body}</details>')
        return f'<div class="entry" id="{aid}"><div class="head">{head}</div>{body}</div>'

    def nav(self, depth, here):
        up = "../" * depth
        parts = ['<nav>', f'<div><a href="{up}index.html"><b>CertiMoon review</b></a></div>',
                 '<h2>Search</h2><input id="search" placeholder="a name…" autocomplete="off">',
                 '<ul id="results"></ul>']
        for title, es in [("Theorems", self.theorems), ("Examples", self.examples)]:
            if not es:
                continue
            parts.append(f'<h2>{title}</h2><ul>')
            for e in es:
                p = f"review/{e['name']}.html"
                cls = ' class="here"' if p == here else ""
                parts.append(f'<li><a{cls} href="{up}{esc(p)}">{esc(e["name"])}</a></li>')
            parts.append('</ul>')
        for pkg in PACKAGES:
            parts.append(f'<h2>{esc(pkg)}</h2><ul>')
            for p, f, page in self.pages:
                if p != pkg:
                    continue
                cls = ' class="here"' if page == here else ""
                parts.append(f'<li><a{cls} href="{up}{esc(page)}">{esc(os.path.basename(f))}</a></li>')
            parts.append('</ul>')
        parts.append('</nav>')
        return "".join(parts)

    def document(self, title, depth, here, content, fragment=False):
        """A page; with `fragment`, without the doctype, html, head and body
        tags (for a host that wraps the entry page in its own)."""
        up = "../" * depth
        head = (f'<title>{esc(title)}</title>'
                f'<meta name="claude:viewport-fit-sides" content="cover">'
                f'<link rel="stylesheet" href="{up}style.css">')
        body = (f'<div class="layout">{self.nav(depth, here)}<main>{content}</main></div>'
                f'<script>var ROOT = "{up}";</script><script src="{up}search.js"></script>'
                f'<script src="{up}search_index.js"></script>')
        if fragment:
            return head + body
        return (f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
                f'<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
                f'{head}</head><body>{body}</body></html>')

    def file_page(self, pkg, file, page):
        depth = page.count("/")
        es = [e for e in self.entries if e["page"] == page]
        counts = {}
        for e in es:
            counts[e["kind"]] = counts.get(e["kind"], 0) + 1
        summary = ", ".join(f"{n} {k}{'s' if n > 1 else ''}" for k, n in counts.items())
        out = [f'<h1>{esc(file)}</h1>',
               f'<p class="muted">{esc(summary)}. Lemmas are folded: the kernel checks them, '
               f'and a review need not read them.</p>']
        section = None
        for e in es:
            if e["section"] != section:
                section = e["section"]
                out.append(f'<h2 class="section">{esc(section)}</h2>')
            out.append(self.entry_html(e, depth))
        return self.document(file, depth, page, "".join(out))

    def closure(self, e):
        """The defining entries `e`'s statement depends on, in listing order,
        and the constants left that no entry defines (hol_light's), as
        package logic computed them."""
        return [self.by_key[k] for k in e.get("depends", [])], e.get("outside", [])

    def depends_summary(self, deps):
        by_pkg = {}
        for d in deps:
            by_pkg[d["package"]] = by_pkg.get(d["package"], 0) + 1
        return (f'{len(deps)} definitions ('
                + ", ".join(f"{n} in {p}" for p, n in by_pkg.items()) + ')')

    def review_page(self, e):
        depth = 1
        page = f"review/{e['name']}.html"
        deps, outside = self.closure(e)
        here = {id(d) for d in deps} | {id(e)}
        out = [f'<h1>{esc(e["name"])}</h1>',
               '<div class="note">To trust this theorem, read its statement and every definition '
               'below: they are all it depends on, found by following the constants of the '
               'statement to the entries that define them. The proofs need no reading: the '
               'kernel checks them, and no axioms are added.</div>',
               self.entry_html(e, depth, fold_lemmas=False, here=here)]
        # the code the statement is about first, then the rest in listing order
        programs = [d for d in deps if d["kind"] == "program"]
        if programs:
            out.append('<h2 class="section">The code</h2>')
            out.extend(self.entry_html(d, depth, here=here) for d in programs)
        out.append(f'<h2 class="section">What it depends on: {self.depends_summary(deps)}</h2>')
        section = None
        for d in deps:
            if d["kind"] == "program":
                continue
            key = (d["package"], d["section"])
            if key != section:
                section = key
                out.append(f'<h2 class="section">{esc(d["package"])}: {esc(d["section"])}</h2>')
            out.append(self.entry_html(d, depth, here=here))
        if outside:
            out.append('<h2 class="section">From hol_light</h2>'
                       '<p class="muted">Constants of hol_light\'s libraries, trusted as hol_light '
                       'defines them: ' + ", ".join(f"<code>{esc(c)}</code>" for c in outside) + '</p>')
        return self.document(e["name"], depth, page, "".join(out))

    def index_page(self, fragment=False):
        n = {k: 0 for k in ["definition", "relation", "program", "lemma", "theorem", "example"]}
        for e in self.entries:
            if e["kind"] == "program":
                n["program"] += 1
            elif e["kind"] in DEFINING:
                n["definition" if e["kind"] != "relation" else "relation"] += 1
            elif e["kind"] in n:
                n[e["kind"]] += 1
        out = ['<h1>CertiMoon: what is defined and proved</h1>',
               '<div class="note">A theorem here trusts hol_light\'s kernel, the definitions its '
               'statement depends on, and its statement; nothing else. Package <b>wasm</b> is '
               'WasmCert\'s WebAssembly semantics ported from Isabelle; package <b>logic</b> is a '
               'separation logic proved sound against it. Neither adds an axiom. The proofs are '
               'checked by the kernel when the packages load, so a review reads definitions and '
               'statements, not proofs.</div>',
               f'<p>{n["definition"]} definitions and datatypes, {count(n["relation"], "relation")}, '
               f'{count(n["program"], "program")}, {count(n["lemma"], "lemma")}, {count(n["theorem"], "closed theorem")} and '
               f'{count(n["example"], "example")}.</p>',
               '<h2 class="section">Closed theorems</h2><p class="muted">What the verified '
               'programs do, stated about their runs (<code>reduce_trans</code>), with no '
               'assertion or triple: these are the results to review.</p>']
        for e in self.theorems:
            deps, _ = self.closure(e)
            out.append(self.entry_html(e, 0, fold_lemmas=False))
            out.append(f'<p><a href="review/{esc(e["name"])}.html">What {esc(e["name"])} depends on: '
                       f'{self.depends_summary(deps)}</a></p>')
        out.append('<h2 class="section">Examples</h2><p class="muted">Triples of verified '
                   'programs, stated in the program logic. A triple says what the runs do through '
                   'the logic\'s adequacy theorems, so its review also reads the logic\'s '
                   'definitions; a closed theorem says it directly.</p>'
                   '<table><tr><th>Example</th><th>Depends on</th><th>Source</th></tr>')
        for e in self.examples:
            deps, _ = self.closure(e)
            out.append(f'<tr><td><a href="review/{esc(e["name"])}.html"><code>{esc(e["name"])}</code></a></td>'
                       f'<td>{len(deps)} definitions</td><td>{self.source_link(e)}</td></tr>')
        out.append('</table>')
        for pkg in PACKAGES:
            out.append(f'<h2 class="section">Package {esc(pkg)}</h2><table>'
                       '<tr><th>File</th><th>Definitions</th><th>Lemmas</th></tr>')
            for p, f, page in self.pages:
                if p != pkg:
                    continue
                es = [e for e in self.entries if e["page"] == page]
                d = sum(1 for e in es if e["kind"] in DEFINING)
                lm = sum(1 for e in es if e["kind"] in ("lemma", "theorem", "example"))
                out.append(f'<tr><td><a href="{esc(page)}">{esc(f)}</a></td><td>{d}</td><td>{lm}</td></tr>')
            out.append('</table>')
        return self.document("CertiMoon review", 0, "index.html", "".join(out), fragment)

    def search_index(self):
        items = [[e["name"], self.href(e, 0)] for e in self.entries]
        return "var SEARCH = " + json.dumps(items) + ";\n"


def count(n, noun):
    """`n noun`, plural unless n is 1."""
    return f"{n} {noun}" + ("" if n == 1 else "s")


def page_of(file):
    """wasm/ast.mbt -> wasm/ast.html; logic/example_fact.mbt -> logic/example_fact.html"""
    return re.sub(r"\.mbt$", ".html", file)


def write(path, text):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w") as f:
        f.write(text)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", default="_site")
    ap.add_argument("--root", default=".")
    ap.add_argument("--source-url", default="https://github.com/moonbit-community/certimoon/blob/main/")
    ap.add_argument("--fragment-index", action="store_true",
                    help="write index.html without its doctype, html, head and body tags")
    args = ap.parse_args()
    site = Site(args.root, args.source_url)
    write(os.path.join(args.out, "style.css"), CSS)
    write(os.path.join(args.out, "search.js"), SEARCH_JS)
    write(os.path.join(args.out, "search_index.js"), site.search_index())
    write(os.path.join(args.out, "index.html"), site.index_page(args.fragment_index))
    for pkg, file, page in site.pages:
        write(os.path.join(args.out, page), site.file_page(pkg, file, page))
    for e in site.reviewed:
        write(os.path.join(args.out, "review", e["name"] + ".html"), site.review_page(e))
    print(f"wrote {len(site.pages)} file pages and {len(site.reviewed)} review pages to {args.out}",
          file=sys.stderr)


main()
