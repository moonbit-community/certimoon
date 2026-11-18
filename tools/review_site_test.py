import json
from pathlib import Path
import tempfile
import unittest

from review_site import Site


class ReviewSiteTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.definition = dict(kind="definition", name="join", file="algebra/join.mbt",
                               line=1, defines=["join"], uses=[], statement="join(p, q) == p && q")
        self.text = "∀ p : Bool, (p <*> q) && 2 * 3 == 6"
        self.theorem = dict(kind="theorem", name="join_example", file="algebra/example.mbt",
                            line=2, defines=[], uses=["join"], statement=self.text,
                            depends=["algebra/join"], outside=[],
                            references=[dict(start=self.text.index("<*>"), length=3, constant="join")],
                            canonical_statement="∀ p : Bool, join(p, q) && 2 * 3 == 6")
        self.write()

    def write(self):
        (self.root / "algebra.json").write_text(json.dumps(
            dict(package="algebra", entries=[self.definition, self.theorem])))

    def site(self):
        return Site(str(self.root), "https://example.org/source/",
                    theories=["algebra.json"], title="Algebra <review>")

    def test_generic_inputs_and_title(self):
        site = self.site()
        self.assertEqual(site.packages, ["algebra"])
        page = site.index_page()
        self.assertIn("Algebra &lt;review&gt;", page)
        self.assertIn("Package algebra", page)
        self.assertNotIn("WebAssembly semantics", page)
        self.assertNotIn("no axioms", site.review_page(site.theorems[0]))

    def test_symbol_reference_and_original_statement(self):
        site = self.site()
        theorem = site.theorems[0]
        page = site.review_page(theorem)
        self.assertIn('href="#e-join" title="definition join">&lt;*&gt;</a>', page)
        self.assertIn("2 * 3 == 6", page)
        self.assertIn("<summary>Original statement</summary>", page)
        self.assertIn("join(p, q)", page)

    def test_entries_without_notation_keep_existing_markup(self):
        self.theorem.pop("references")
        self.theorem.pop("canonical_statement")
        self.write()
        site = self.site()
        page = site.entry_html(site.theorems[0], 0)
        self.assertNotIn("Original statement", page)
        self.assertIn("&lt;*&gt;", page)

    def test_invalid_references_fail_explicitly(self):
        self.theorem["references"][0]["start"] = len(self.text)
        self.write()
        site = self.site()
        with self.assertRaisesRegex(ValueError, "invalid notation reference"):
            site.linked(site.theorems[0], 0)


if __name__ == "__main__":
    unittest.main()
