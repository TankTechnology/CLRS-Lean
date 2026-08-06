#!/usr/bin/env python3
"""Create a current-source Verso module map from built literate JSON files."""

from __future__ import annotations

import argparse
from pathlib import Path


def _source_path(module: str, source_dir: Path) -> Path:
    """Return the Lean source path corresponding to one dotted module name."""

    return source_dir.joinpath(*module.split(".")).with_suffix(".lean")


def _prune_json_artifacts(json_path: Path) -> None:
    """Remove one orphan JSON file and only its exact Lake sidecars."""

    for path in (
        json_path,
        json_path.with_suffix(".json.hash"),
        json_path.with_suffix(".json.trace"),
    ):
        if path.is_file():
            path.unlink()


def write_module_map(
    literate_root: Path,
    output: Path,
    source_dir: Path,
    *,
    prune_orphans: bool = False,
) -> int:
    literate_root = literate_root.resolve()
    if not literate_root.is_dir():
        raise ValueError(f"literate JSON directory does not exist: {literate_root}")
    project_root = Path.cwd().resolve()
    modules: list[tuple[str, Path]] = []
    for json_path in sorted(literate_root.rglob("*.json")):
        relative = json_path.relative_to(literate_root)
        module = ".".join(relative.with_suffix("").parts)
        if not _source_path(module, source_dir).is_file():
            if prune_orphans:
                _prune_json_artifacts(json_path)
            continue
        modules.append((module, json_path))
    rows: list[str] = []
    for module, json_path in sorted(modules):
        try:
            portable_json = json_path.resolve().relative_to(project_root)
            json_text = portable_json.as_posix()
        except ValueError:
            json_text = str(json_path.resolve())
        rows.append(f"{module}\t{json_text}\t{source_dir.as_posix()}\n")
    if not rows:
        raise ValueError(f"no literate JSON files found under {literate_root}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(rows), encoding="utf-8")
    return len(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("literate_root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--source-dir", type=Path, default=Path("."))
    parser.add_argument(
        "--prune-orphans",
        action="store_true",
        help="remove JSON and Lake sidecars whose corresponding Lean source no longer exists",
    )
    args = parser.parse_args()
    try:
        count = write_module_map(
            args.literate_root,
            args.output,
            args.source_dir,
            prune_orphans=args.prune_orphans,
        )
    except ValueError as exc:
        parser.error(str(exc))
    print(f"wrote {count} modules to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
