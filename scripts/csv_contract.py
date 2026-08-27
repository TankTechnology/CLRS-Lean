"""Strict helpers for machine-readable repository CSV contracts."""

from __future__ import annotations

import csv
from pathlib import Path


def load_strict_dict_rows(
    path: Path, expected_header: list[str]
) -> list[dict[str, str]]:
    """Load a CSV and reject header mismatches and overflow fields."""
    if not path.is_file():
        raise ValueError(f"missing file: {path.name}")
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != expected_header:
            raise ValueError(
                f"unexpected header in {path.name}: {reader.fieldnames}; "
                f"expected {expected_header}"
            )
        rows: list[dict[str, str]] = []
        for line, raw_row in enumerate(reader, start=2):
            extras = raw_row.pop(None, None)
            if extras is not None:
                rendered = ", ".join(value for value in extras if value is not None)
                raise ValueError(
                    f"{path.name} line {line}: unexpected extra fields: {rendered}"
                )
            rows.append({field: raw_row[field] or "" for field in expected_header})
        return rows
