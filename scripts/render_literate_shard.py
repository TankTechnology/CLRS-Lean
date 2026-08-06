#!/usr/bin/env python3
"""Render one full-context Verso shard and record immutable provenance."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any


HOVER_ID_STRIDE = 1_000_000_000


def _load_manifest(path: Path) -> dict[str, Any]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
        raise ValueError(f"unsupported shard manifest: {path}")
    return manifest


def render_shard(
    executable: Path,
    module_map: Path,
    config: Path,
    manifest_path: Path,
    shard_index: int,
    output: Path,
) -> dict[str, Any]:
    """Invoke the patched renderer for one manifest assignment."""
    manifest = _load_manifest(manifest_path)
    assignments = {
        int(entry["index"]): entry
        for entry in manifest.get("shards", [])
        if isinstance(entry, dict) and "index" in entry
    }
    if shard_index not in assignments:
        raise ValueError(f"shard {shard_index} is absent from {manifest_path}")
    assignment = assignments[shard_index]
    emit_list = manifest_path.parent / str(assignment["module_file"])
    listed_modules = [
        line.strip()
        for line in emit_list.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    expected_modules = list(assignment["modules"])
    if listed_modules != expected_modules:
        raise ValueError(f"shard {shard_index} emit list differs from the signed manifest")
    if not executable.is_file():
        raise ValueError(f"renderer executable does not exist: {executable}")

    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{output.name}.render-", dir=output.parent))
    html = staging / "html"
    metadata = staging / "verso-docs.json"
    command = [
        str(executable.resolve()),
        str(html),
        str(module_map.resolve()),
        str(config.resolve()),
        "--emit-list",
        str(emit_list.resolve()),
        "--metadata-out",
        str(metadata),
        "--hover-id-offset",
        str(shard_index * HOVER_ID_STRIDE),
    ]
    if shard_index == 0:
        command.append("--coordinator")

    started = time.monotonic()
    try:
        subprocess.run(command, check=True)
        duration = time.monotonic() - started
        byte_count = sum(path.stat().st_size for path in html.rglob("*") if path.is_file())
        record: dict[str, Any] = {
            "schema_version": 1,
            "shard_index": shard_index,
            "input_digest": manifest["input_digest"],
            "modules": listed_modules,
            "duration_seconds": round(duration, 3),
            "byte_count": byte_count,
            "output_dir": "html",
            "metadata_path": "verso-docs.json",
            "hover_id_offset": shard_index * HOVER_ID_STRIDE,
        }
        (staging / "shard-record.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        if output.exists():
            shutil.rmtree(output)
        os.replace(staging, output)
        print(
            f"rendered shard {shard_index}: {len(listed_modules)} modules, "
            f"{byte_count} bytes, {duration:.1f}s"
        )
        return record
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", required=True, type=Path)
    parser.add_argument("--module-map", required=True, type=Path)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--shard-index", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        render_shard(
            args.executable,
            args.module_map,
            args.config,
            args.manifest,
            args.shard_index,
            args.output,
        )
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.error(str(exc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
