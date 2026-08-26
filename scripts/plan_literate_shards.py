#!/usr/bin/env python3
"""Plan deterministic, chapter-affine shards for Verso literate rendering."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHAPTER_RE = re.compile(r"^(CLRSLean(?:\.FourthEdition)?\.Chapter_\d{2})(?:\.|$)")


@dataclass(frozen=True, order=True)
class ModuleCost:
    """One module and the measured size of its literate JSON input."""

    name: str
    json_path: Path
    size_bytes: int

    @property
    def affinity(self) -> str:
        match = CHAPTER_RE.match(self.name)
        if match is not None:
            return match.group(1)
        parts = self.name.split(".")
        return ".".join(parts[:2]) if len(parts) > 1 else self.name


def _resolve_input(path_text: str, module_map: Path) -> Path:
    path = Path(path_text)
    if path.is_absolute():
        return path
    cwd_candidate = Path.cwd() / path
    if cwd_candidate.is_file():
        return cwd_candidate.resolve()
    return (module_map.parent / path).resolve()


def discover_modules(module_map: Path) -> list[ModuleCost]:
    """Read ``name<TAB>json<TAB>source`` rows and measure every JSON input."""
    module_map = module_map.resolve()
    modules: list[ModuleCost] = []
    seen: set[str] = set()
    for line_number, raw_line in enumerate(
        module_map.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not raw_line.strip():
            continue
        fields = raw_line.split("\t")
        if len(fields) < 2:
            raise ValueError(f"{module_map}:{line_number}: expected tab-separated module and JSON path")
        name = fields[0].strip()
        if not name:
            raise ValueError(f"{module_map}:{line_number}: empty module name")
        if name in seen:
            raise ValueError(f"{module_map}:{line_number}: duplicate module {name}")
        seen.add(name)
        json_path = _resolve_input(fields[1].strip(), module_map)
        if not json_path.is_file():
            raise ValueError(f"{module_map}:{line_number}: JSON input does not exist: {json_path}")
        modules.append(ModuleCost(name, json_path, json_path.stat().st_size))
    return sorted(modules, key=lambda module: module.name)


def partition_modules(modules: list[ModuleCost], shard_count: int) -> list[list[ModuleCost]]:
    """Balance modules while keeping non-oversized affinity groups together."""
    if shard_count <= 0:
        raise ValueError("shard count must be positive")
    groups: dict[str, list[ModuleCost]] = {}
    for module in modules:
        groups.setdefault(module.affinity, []).append(module)

    total_bytes = sum(module.size_bytes for module in modules)
    ideal_load = (total_bytes + shard_count - 1) // shard_count
    planning_units: list[tuple[str, list[ModuleCost]]] = []
    for affinity, group in sorted(groups.items()):
        ordered_group = sorted(group, key=lambda module: module.name)
        group_load = sum(module.size_bytes for module in ordered_group)
        if len(ordered_group) > 1 and group_load > ideal_load:
            planning_units.extend(
                (f"{affinity}\0{module.name}", [module]) for module in ordered_group
            )
        else:
            planning_units.append((affinity, ordered_group))

    ordered_units = sorted(
        planning_units,
        key=lambda item: (-sum(module.size_bytes for module in item[1]), item[0]),
    )
    shards: list[list[ModuleCost]] = [[] for _ in range(shard_count)]
    loads = [0] * shard_count
    for _, group in ordered_units:
        target = min(range(shard_count), key=lambda index: (loads[index], index))
        shards[target].extend(group)
        loads[target] += sum(module.size_bytes for module in group)
    return [sorted(shard, key=lambda module: module.name) for shard in shards]


def compute_input_digest(module_map: Path, modules: list[ModuleCost], inputs: list[Path]) -> str:
    """Hash configuration inputs and all literate JSON files with stable labels."""
    digest = hashlib.sha256()
    files = [("module-map", module_map.resolve()), *[(path.name, path.resolve()) for path in inputs]]
    for label, path in files:
        digest.update(label.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    for module in sorted(modules, key=lambda item: item.name):
        digest.update(module.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(hashlib.sha256(module.json_path.read_bytes()).digest())
    return digest.hexdigest()


def write_plan(
    modules: list[ModuleCost],
    output: Path,
    *,
    input_digest: str,
    shard_count: int = 4,
) -> dict[str, object]:
    """Write emit lists and a canonical JSON manifest, returning the manifest."""
    shards = partition_modules(modules, shard_count)
    output.mkdir(parents=True, exist_ok=True)
    shard_entries: list[dict[str, object]] = []
    loads: list[int] = []
    for index, shard in enumerate(shards):
        names = [module.name for module in shard]
        load = sum(module.size_bytes for module in shard)
        loads.append(load)
        module_file = f"shard-{index}.txt"
        (output / module_file).write_text(
            "".join(f"{name}\n" for name in names), encoding="utf-8"
        )
        shard_entries.append(
            {
                "index": index,
                "module_file": module_file,
                "modules": names,
                "estimated_bytes": load,
            }
        )
    manifest: dict[str, object] = {
        "schema_version": 1,
        "input_digest": input_digest,
        "shard_count": shard_count,
        "module_count": len(modules),
        "total_input_bytes": sum(module.size_bytes for module in modules),
        "max_load_skew_bytes": (max(loads) - min(loads)) if loads else 0,
        "shards": shard_entries,
    }
    (output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module_map", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--shards", type=int, default=4)
    parser.add_argument(
        "--digest-input",
        action="append",
        type=Path,
        default=[],
        help="Configuration input included in the immutable plan digest (repeatable).",
    )
    args = parser.parse_args()
    modules = discover_modules(args.module_map)
    digest = compute_input_digest(args.module_map, modules, args.digest_input)
    manifest = write_plan(
        modules,
        args.output,
        input_digest=digest,
        shard_count=args.shards,
    )
    loads = [int(shard["estimated_bytes"]) for shard in manifest["shards"]]
    print(
        f"planned {manifest['module_count']} modules across {args.shards} shards; "
        f"loads={loads}; max skew={manifest['max_load_skew_bytes']} bytes; "
        f"digest={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
