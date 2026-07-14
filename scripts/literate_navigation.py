"""Reader-facing navigation policy for generated Verso pages."""

from __future__ import annotations

import re


CHAPTER_MODULE_RE = re.compile(r"Chapter_[0-9][0-9]")


def is_reader_sidebar_module(module_name: str) -> bool:
    """Return whether a Lean module belongs in the reader-facing sidebar."""
    parts = module_name.split(".")
    if parts == ["CLRSLean"]:
        return True
    if len(parts) == 2 and parts[0] == "CLRSLean":
        return True
    return (
        len(parts) == 3
        and parts[0] == "CLRSLean"
        and CHAPTER_MODULE_RE.fullmatch(parts[1]) is not None
        and parts[2].startswith("Section_")
    )
