"""Machine-readable online/supplementary-material ledger helpers."""

from __future__ import annotations

from pathlib import Path

from csv_contract import load_strict_dict_rows


ROOT = Path(__file__).resolve().parents[1]
ONLINE_PATH = ROOT / "docs" / "clrs-online-material.csv"
ONLINE_HEADER = [
    "topic_id",
    "title",
    "source_modules",
    "legacy_location",
    "tracked_key_theorems",
    "coverage_note",
]


def split_source_modules(raw: str) -> list[str]:
    return [part.strip() for part in raw.split(";") if part.strip()]


def load_online_rows(root: Path = ROOT) -> list[dict[str, str]]:
    return load_strict_dict_rows(
        root / "docs" / "clrs-online-material.csv", ONLINE_HEADER
    )


def online_tracked_total(rows: list[dict[str, str]] | None = None) -> int:
    material = load_online_rows() if rows is None else rows
    return sum(int(row["tracked_key_theorems"]) for row in material)
