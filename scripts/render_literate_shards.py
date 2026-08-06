#!/usr/bin/env python3
"""Run a complete local Verso shard plan with bounded parallelism."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SINGLE_RUNNER = ROOT / "scripts" / "render_literate_shard.py"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", required=True, type=Path)
    parser.add_argument("--module-map", required=True, type=Path)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error("--jobs must be between 1 and 4")
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    indices = sorted(int(entry["index"]) for entry in manifest["shards"])

    def command(index: int) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(SINGLE_RUNNER),
                "--executable",
                str(args.executable),
                "--module-map",
                str(args.module_map),
                "--config",
                str(args.config),
                "--manifest",
                str(args.manifest),
                "--shard-index",
                str(index),
                "--output",
                str(args.output / f"shard-{index}"),
            ],
            text=True,
            capture_output=True,
            check=False,
        )

    failures = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(command, index): index for index in indices}
        for future in as_completed(futures):
            index = futures[future]
            result = future.result()
            print(result.stdout, end="")
            if result.returncode != 0:
                failures += 1
                print(result.stderr, end="", file=sys.stderr)
                print(f"shard {index} failed", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
