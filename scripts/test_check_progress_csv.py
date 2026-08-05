import unittest

from check_progress_csv import sections_from_filename


class SectionsFromFilenameTest(unittest.TestCase):
    def test_expands_section_range_filename(self) -> None:
        sections = sections_from_filename("Section_05_1_4_Probabilistic_Analysis.lean")

        self.assertEqual(sections, {"5.1", "5.2", "5.3", "5.4"})

    def test_compatibility_aggregator_excludes_unadvertised_section(self) -> None:
        sections = sections_from_filename("Section_27_2_4_Algorithms.lean")

        self.assertEqual(sections, {"27.2", "27.3"})


if __name__ == "__main__":
    unittest.main()
