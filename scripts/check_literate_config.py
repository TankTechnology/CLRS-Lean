#!/usr/bin/env python3
"""Validate the fourth-edition-first Verso navigation contract."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FOURTH_EDITION = "CLRSLean.FourthEdition"
PRIMARY_ROOT_MODULES = (
    FOURTH_EDITION,
    "CLRSLean.OnlineMaterial",
    "CLRSLean.ProofPatterns",
    "CLRSLean.Probability",
    "CLRSLean.Extensions",
    "CLRSLean.Progress",
    "CLRSLean.Status",
    "CLRSLean.Workflow",
)
FOURTH_EDITION_CHAPTER_TITLES = (
    "The Role of Algorithms in Computing",
    "Getting Started",
    "Characterizing Running Times",
    "Divide-and-Conquer",
    "Probabilistic Analysis and Randomized Algorithms",
    "Heapsort",
    "Quicksort",
    "Sorting in Linear Time",
    "Medians and Order Statistics",
    "Elementary Data Structures",
    "Hash Tables",
    "Binary Search Trees",
    "Red-Black Trees",
    "Dynamic Programming",
    "Greedy Algorithms",
    "Amortized Analysis",
    "Augmenting Data Structures",
    "B-Trees",
    "Data Structures for Disjoint Sets",
    "Elementary Graph Algorithms",
    "Minimum Spanning Trees",
    "Single-Source Shortest Paths",
    "All-Pairs Shortest Paths",
    "Maximum Flow",
    "Matchings in Bipartite Graphs",
    "Parallel Algorithms",
    "Online Algorithms",
    "Matrix Operations",
    "Linear Programming",
    "Polynomials and the FFT",
    "Number-Theoretic Algorithms",
    "String Matching",
    "Machine-Learning Algorithms",
    "NP-Completeness",
    "Approximation Algorithms",
)
FOURTH_EDITION_CHAPTERS = tuple(
    f"{FOURTH_EDITION}.Chapter_{chapter:02d}" for chapter in range(1, 36)
)


def parse_order_children(text: str) -> dict[str, list[str]]:
    """Parse the module arrays in ``[order_children]``."""
    blocks: dict[str, list[str]] = {}
    pattern = re.compile(r'^"([^"]+)"\s*=\s*\[(.*?)^\]', re.MULTILINE | re.DOTALL)
    for match in pattern.finditer(text):
        blocks[match.group(1)] = re.findall(r'"([^"]+)"', match.group(2))
    return blocks


def parse_module_titles(text: str) -> dict[str, str]:
    """Parse module names and their configured reader titles."""
    return dict(
        re.findall(
            r'^\[modules\."([^"]+)"\]\s*\ntitle\s*=\s*"([^"]+)"',
            text,
            re.MULTILINE,
        )
    )


def validate_config(config_text: str, fourth_edition_source: str) -> list[str]:
    """Return fourth-edition navigation violations in deterministic order."""
    errors: list[str] = []
    order_children = parse_order_children(config_text)
    titles = parse_module_titles(config_text)

    actual_root = order_children.get("CLRSLean", [])
    if actual_root != list(PRIMARY_ROOT_MODULES):
        errors.append(
            "primary root order must be fourth edition, online material, and support pages: "
            + ", ".join(PRIMARY_ROOT_MODULES)
        )

    actual_chapters = order_children.get(FOURTH_EDITION, [])
    if actual_chapters != list(FOURTH_EDITION_CHAPTERS):
        errors.append(
            "fourth-edition chapter order must contain Chapters 1--35 exactly once"
        )

    imported_chapters = re.findall(
        rf"^import\s+({re.escape(FOURTH_EDITION)}\.Chapter_[^\s]+)",
        fourth_edition_source,
        re.MULTILINE,
    )
    if imported_chapters != list(FOURTH_EDITION_CHAPTERS):
        errors.append(
            "CLRSLean.FourthEdition imports must contain Chapters 1--35 in order"
        )

    expected_root_titles = {
        FOURTH_EDITION: "CLRS Fourth Edition",
        "CLRSLean.OnlineMaterial": "Online Material",
    }
    for module, expected in expected_root_titles.items():
        actual = titles.get(module)
        if actual != expected:
            errors.append(f'{module} title must be "{expected}", got {actual!r}')

    for chapter, (module, chapter_title) in enumerate(
        zip(FOURTH_EDITION_CHAPTERS, FOURTH_EDITION_CHAPTER_TITLES), start=1
    ):
        expected = f"Chapter {chapter}. {chapter_title}"
        actual = titles.get(module)
        if actual != expected:
            errors.append(f'{module} title must be "{expected}", got {actual!r}')

    return errors


def _module_source(root: Path, module: str) -> Path:
    parts = module.split(".")
    if parts == ["CLRSLean"]:
        return root / "CLRSLean.lean"
    return root / Path(*parts[:-1]) / f"{parts[-1]}.lean"


def validate_repository(root: Path) -> list[str]:
    """Validate navigation metadata and the public module files it names."""
    config_path = root / "literate.toml"
    fourth_edition_path = root / "CLRSLean" / "FourthEdition.lean"
    missing_inputs = [
        path for path in (config_path, fourth_edition_path) if not path.is_file()
    ]
    if missing_inputs:
        return [f"missing literate config input: {path}" for path in missing_inputs]

    config_text = config_path.read_text()
    errors = validate_config(config_text, fourth_edition_path.read_text())
    titles = parse_module_titles(config_text)

    required_modules = (FOURTH_EDITION, "CLRSLean.OnlineMaterial") + FOURTH_EDITION_CHAPTERS
    for module in required_modules:
        if not _module_source(root, module).is_file():
            errors.append(f"configured reader module has no source file: {module}")

    landing_path = root / "CLRSLean.lean"
    if landing_path.is_file():
        legacy_guides = re.findall(
            r"^import\s+(CLRSLean\.Chapter_[0-9][0-9])$",
            landing_path.read_text(),
            re.MULTILINE,
        )
        for module in legacy_guides:
            if module not in titles:
                errors.append(f"legacy compatibility page has no module title: {module}")

    return errors


def main() -> int:
    errors = validate_repository(ROOT)
    if errors:
        print("literate config errors:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print("Literate config OK: fourth-edition reader navigation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
