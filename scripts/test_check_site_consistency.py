import unittest

import check_site_consistency


class LegacyChapterNavigationTests(unittest.TestCase):
    def _errors(
        self,
        chapter_modules: list[str],
        root_modules: list[str],
        titled_modules: set[str],
        landing_text: str,
    ) -> list[str]:
        validator = getattr(
            check_site_consistency, "legacy_chapter_navigation_errors", None
        )
        if validator is None:
            self.fail("legacy chapter navigation validator is missing")
        return validator(
            chapter_modules, root_modules, titled_modules, landing_text
        )

    def test_accepts_imported_titled_legacy_page_outside_primary_root(self) -> None:
        module = "CLRSLean.Chapter_19"

        self.assertEqual(
            [],
            self._errors(
                [module],
                ["CLRSLean.FourthEdition", "CLRSLean.OnlineMaterial"],
                {module},
                f"import {module}\n",
            ),
        )

    def test_rejects_legacy_page_in_primary_root(self) -> None:
        module = "CLRSLean.Chapter_19"

        self.assertTrue(
            any(
                "must be hidden from the primary root" in error
                for error in self._errors(
                    [module], [module], {module}, f"import {module}\n"
                )
            )
        )

    def test_requires_import_and_title_for_renderable_legacy_page(self) -> None:
        module = "CLRSLean.Chapter_19"
        errors = self._errors([module], [], set(), "")

        self.assertTrue(any("missing import" in error for error in errors))
        self.assertTrue(any("no module title" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
