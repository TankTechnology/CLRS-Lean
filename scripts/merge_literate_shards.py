#!/usr/bin/env python3
"""Validate and atomically merge independently rendered Verso HTML shards."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any


SHARED_INDEX_PAGES = {Path("index.html"), Path("search/index.html")}


def _load_json(path: Path, errors: list[str], label: str) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"{label}: cannot read JSON {path}: {exc}")
        return None


def _file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def merge_shards(manifest: Path, shard_roots: list[Path], output: Path) -> list[str]:
    """Validate shard coverage/digests/collisions, then replace ``output``."""
    errors: list[str] = []
    plan = _load_json(manifest, errors, "manifest")
    if not isinstance(plan, dict):
        return sorted(set(errors or ["manifest: expected a JSON object"]))
    expected_digest = plan.get("input_digest")
    expected_shards = {
        int(shard["index"]): list(shard["modules"])
        for shard in plan.get("shards", [])
        if isinstance(shard, dict) and "index" in shard and "modules" in shard
    }
    if len(expected_shards) != plan.get("shard_count"):
        errors.append("manifest: shard_count does not match shard entries")

    records: dict[int, tuple[Path, dict[str, Any]]] = {}
    all_modules: list[str] = []
    file_sources: dict[Path, tuple[str, Path]] = {}
    merged_metadata: dict[str, Any] = {}
    for root in sorted((path.resolve() for path in shard_roots), key=str):
        record_path = root / "shard-record.json"
        record = _load_json(record_path, errors, "shard record")
        if not isinstance(record, dict):
            continue
        try:
            index = int(record["shard_index"])
        except (KeyError, TypeError, ValueError):
            errors.append(f"{record_path}: invalid or missing shard_index")
            continue
        if index in records:
            errors.append(f"duplicate shard index: {index}")
            continue
        records[index] = (root, record)
        if record.get("input_digest") != expected_digest:
            errors.append(f"shard {index}: input digest does not match manifest digest")
        modules = record.get("modules")
        if not isinstance(modules, list) or not all(isinstance(name, str) for name in modules):
            errors.append(f"shard {index}: modules must be a string list")
            modules = []
        all_modules.extend(modules)
        if index in expected_shards and sorted(modules) != sorted(expected_shards[index]):
            errors.append(f"shard {index}: module list does not match its manifest assignment")

        html_root = root / str(record.get("output_dir", "html"))
        if not html_root.is_dir():
            errors.append(f"shard {index}: output directory does not exist: {html_root}")
        else:
            output_files = sorted(path for path in html_root.rglob("*") if path.is_file())
            if index in expected_shards:
                expected_pages = {
                    Path(*module.split("."), "index.html")
                    for module in expected_shards[index]
                }
                actual_pages = {
                    source.relative_to(html_root)
                    for source in output_files
                    if source.name == "index.html"
                    and source.relative_to(html_root) not in SHARED_INDEX_PAGES
                }
                for page in sorted(expected_pages - actual_pages, key=str):
                    errors.append(
                        f"shard {index}: missing rendered module page: {page.as_posix()}"
                    )
                for page in sorted(actual_pages - expected_pages, key=str):
                    errors.append(
                        f"shard {index}: unexpected rendered module page: {page.as_posix()}"
                    )
            for source in output_files:
                relative = source.relative_to(html_root)
                source_digest = _file_digest(source)
                previous = file_sources.get(relative)
                if previous is not None and previous[0] != source_digest:
                    errors.append(f"unequal output collision: {relative.as_posix()}")
                else:
                    file_sources.setdefault(relative, (source_digest, source))

        metadata_path = root / str(record.get("metadata_path", "verso-docs.json"))
        metadata = _load_json(metadata_path, errors, f"shard {index} metadata")
        if metadata is not None and not isinstance(metadata, dict):
            errors.append(f"shard {index}: metadata must be a JSON object")
        elif isinstance(metadata, dict):
            for key in sorted(metadata):
                if key in merged_metadata and merged_metadata[key] != metadata[key]:
                    errors.append(f"unequal metadata key collision: {key}")
                else:
                    merged_metadata.setdefault(key, metadata[key])

    for index in sorted(set(expected_shards) - set(records)):
        errors.append(f"missing shard index: {index}")
    for index in sorted(set(records) - set(expected_shards)):
        errors.append(f"unexpected shard index: {index}")

    expected_modules = {
        module for modules in expected_shards.values() for module in modules
    }
    counts = Counter(all_modules)
    for module, count in sorted(counts.items()):
        if count > 1:
            errors.append(f"duplicate module: {module}")
    for module in sorted(expected_modules - set(counts)):
        errors.append(f"missing module: {module}")
    for module in sorted(set(counts) - expected_modules):
        errors.append(f"unexpected module: {module}")

    errors = sorted(set(errors))
    if errors:
        return errors

    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{output.name}.merge-", dir=output.parent))
    backup = output.with_name(f".{output.name}.previous")
    try:
        for relative, (_, source) in sorted(file_sources.items(), key=lambda item: str(item[0])):
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        (staging / "-verso-docs.json").write_text(
            json.dumps(merged_metadata, separators=(",", ":"), sort_keys=True),
            encoding="utf-8",
        )
        if backup.exists():
            shutil.rmtree(backup)
        if output.exists():
            os.replace(output, backup)
        try:
            os.replace(staging, output)
        except BaseException:
            if backup.exists() and not output.exists():
                os.replace(backup, output)
            raise
        if backup.exists():
            shutil.rmtree(backup)
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    return []


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("shards", nargs="+", type=Path)
    args = parser.parse_args()
    errors = merge_shards(args.manifest, args.shards, args.output)
    if errors:
        for error in errors:
            print(f"error: {error}")
        return 1
    print(f"merged {len(args.shards)} validated shards into {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
