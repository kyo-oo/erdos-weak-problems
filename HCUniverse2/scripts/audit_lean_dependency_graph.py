#!/usr/bin/env python3
"""Audit the real Lean import closure without installing Lean locally.

Run on GitHub Actions. Files are classified by actual imports and Lake roots,
never by the misleading rule that a V2 file makes V1 deletable.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
IGNORED = {".git", ".lake", ".elan", "build", "dist", ".venv"}
LOCAL_PREFIXES = (
    "GST", "Hodge", "CardinalWorlds", "ComparatorSmoke",
    "MonolithBoundary", "Information", "Origin", "waves.",
)
IMPORT = re.compile(r"^\s*import\s+(.+?)(?:\s*--.*)?$")
LEGACY = re.compile(r"(?:Scratch|Legacy|Probe|Test)(?:\.lean)$", re.I)

def main() -> int:
    configuration = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    modules: dict[str, str] = {}
    for f in ROOT.rglob("*.lean"):
        if any(part in IGNORED for part in f.relative_to(ROOT).parts):
            continue
        relative = f.relative_to(ROOT).as_posix()
        modules[relative.removesuffix(".lean").replace("/", ".")] = relative

    imports: dict[str, list[str]] = {}
    reverse: dict[str, list[str]] = collections.defaultdict(list)
    missing: list[dict[str, str]] = []
    for module, relative in sorted(modules.items()):
        contents = (ROOT / relative).read_text(encoding="utf-8")
        direct: list[str] = []
        for line in contents.splitlines():
            match = IMPORT.match(line)
            if not match:
                continue
            for dependency in match.group(1).split():
                if dependency in modules:
                    direct.append(dependency)
                    reverse[dependency].append(module)
                elif dependency.startswith(LOCAL_PREFIXES):
                    missing.append({"file": relative, "import": dependency})
        imports[module] = sorted(set(direct))

    libraries: dict[str, list[str]] = {
        entry["name"]: entry.get("roots", [entry["name"]])
        for entry in configuration.get("lean_lib", [])
    }
    roots: set[str] = set()
    for listed in libraries.values():
        roots.update(module for module in listed if module in modules)
    for target in configuration.get("defaultTargets", []):
        if target in modules:
            roots.add(target)
    for expected in ["HodgeConjecture", "Main", "HCProof"]:
        if expected in modules:
            roots.add(expected)

    reachable: set[str] = set()
    def visit(start: str) -> None:
        if start in reachable:
            return
        reachable.add(start)
        for dep in imports[start]:
            visit(dep)
    for module in sorted(roots):
        visit(module)

    color: dict[str, int] = {}
    cycles: list[list[str]] = []
    stack: list[str] = []
    def detect(m: str) -> None:
        color[m] = 1
        stack.append(m)
        for dep in imports[m]:
            if color.get(dep, 0) == 0:
                detect(dep)
            elif color.get(dep) == 1:
                cycles.append(stack[stack.index(dep):] + [dep])
        stack.pop()
        color[m] = 2
    for module in sorted(modules):
        if color.get(module, 0) == 0:
            detect(module)

    unused = sorted(m for m in modules if m not in reachable)
    candidates = sorted(
        modules[m] for m in unused
        if not reverse[m] and LEGACY.search(modules[m])
    )
    v2foundations = sorted(
        (
            {"foundation": modules[m], "upgrade": modules[m + "V2"],
             "referenced_by_upgrade": m in imports[m + "V2"]}
            for m in modules
            if m + "V2" in modules
        ),
        key=lambda x: x["foundation"],
    )

    output = {
        "lean_files": len(modules),
        "registered_roots": {k: len(v) for k, v in libraries.items()},
        "active_roots": len(roots),
        "reachable_from_roots": len(reachable),
        "not_reachable_from_roots": [modules[m] for m in unused],
        "unreferenced_legacy_candidates_REVIEW_ONLY": candidates,
        "local_missing_imports": missing,
        "import_cycles": cycles,
        "v2_foundation_pairs": v2foundations,
        "modules": {
            modules[m]: {
                "imports": [modules[d] for d in imports[m]],
                "imported_by": [modules[d] for d in sorted(reverse[m])],
                "registered_or_entry_root": m in roots,
                "reachable": m in reachable,
            }
            for m in sorted(modules)
        },
    }
    path = ROOT / "lean-dependency-audit.json"
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")

    summary = [
        "# Advanced GST/Hodge import graph audit",
        "",
        f"- Lean files inspected: **{len(modules)}**",
        f"- Active registered/entry roots: **{len(roots)}**",
        f"- Reachable files: **{len(reachable)}**",
        f"- Unreachable files: **{len(unused)}**",
        f"- Unreferenced legacy candidates for manual review: **{len(candidates)}**",
        f"- Missing local imports: **{len(missing)}**",
        f"- Import cycles: **{len(cycles)}**",
        "",
        "A V2 module importing its foundation requires both sources. No Lean files",
        "are deleted or modified by this audit.",
        "",
        "## Explicit legacy candidates (review only)",
        *[f"- `{p}`" for p in candidates],
        "",
        "See `lean-dependency-audit.json` for all module edges and reachability.",
    ]
    md = ROOT / "lean-dependency-audit.md"
    md.write_text("\n".join(summary) + "\n", encoding="utf-8")
    print("\n".join(summary))
    return 1 if missing or cycles else 0

if __name__ == "__main__":
    sys.exit(main())
