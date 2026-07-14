import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_literate_rendering import check_site


PARENT = "CLRSLean.Chapter_22.Section_22_3_DFS"
CHILD = f"{PARENT}.S1_WhitePath"
CHILD_HREF = "CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/"


def write_module(site_root: Path, module_name: str, html: str) -> Path:
    path = site_root.joinpath(*module_name.split("."), "index.html")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(html, encoding="utf-8")
    return path


class LiterateRenderingCheckTests(unittest.TestCase):
    def test_reports_forbidden_sidebar_module(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(
                site,
                PARENT,
                f"""<nav class="module-tree">
  <div class="leaf"><a href="{CHILD_HREF}" title="{CHILD}">White Path</a></div>
</nav><a href="{CHILD_HREF}">Implementation</a>""",
            )
            write_module(site, CHILD, "<main>White Path</main>")

            failures = check_site(site)

        self.assertTrue(
            any(f"forbidden sidebar module: {CHILD}" in failure for failure in failures)
        )

    def test_reports_unclassified_sidebar_link(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(
                site,
                PARENT,
                """<nav class="module-tree">
  <div class="leaf"><a href="mystery/">Mystery</a></div>
</nav>""",
            )

            failures = check_site(site)

        self.assertTrue(
            any("unclassified sidebar link: mystery/" in failure for failure in failures)
        )

    def test_reports_missing_parent_implementation_link(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(site, PARENT, "<main>DFS</main>")
            write_module(site, CHILD, "<main>White Path</main>")

            failures = check_site(site)

        self.assertTrue(
            any(f"missing implementation link for {CHILD}" in failure for failure in failures)
        )

    def test_accepts_pruned_sidebar_and_parent_link(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(
                site,
                PARENT,
                f"""<nav class="module-tree">
  <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/" title="{PARENT}">22.3</a></div>
</nav><a href="{CHILD_HREF}">White Path</a>""",
            )
            write_module(site, CHILD, "<main>White Path</main>")

            failures = check_site(site)

        self.assertEqual([], failures)

    def test_preserves_raw_markdown_table_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(
                site,
                "CLRSLean.Progress",
                "<p>| Chapter | Status |\n|---|---|</p>",
            )

            failures = check_site(site)

        self.assertTrue(any("raw Markdown table" in failure for failure in failures))


if __name__ == "__main__":
    unittest.main()
