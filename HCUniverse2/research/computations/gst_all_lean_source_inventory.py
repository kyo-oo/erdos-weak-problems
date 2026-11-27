#!/usr/bin/env python3
"""Read and index every tracked Lean file in the GST HC research worktree.

This is a source inventory, not a proof of Lean kernel validity, nor a claim
that 700 complete mathematical arguments have been individually understood.
Pure Python stdlib; GitHub Actions, not a local Lean installation.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
names = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=ROOT).decode().split("\0")
paths = sorted([p for p in names if p])
declaration = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*"
    r"(theorem|lemma|def|structure|class|axiom|opaque|abbrev|instance|inductive)\s+([^\s:(]+)"
)
tags = {
    "original_X": r"(?:OriginalX|ActualX|original.X|actual.X|arbitrary.X)",
    "native_cycles": r"(?:Chow|CycleClass|codimensionCycles|NativeCycle)",
    "k_theory": r"(?:K0|PerfectComplex|Todd|Chern|GRR|FiniteFlat)",
    "hilbert_sheaf": r"(?:Hilbert|Semiregular|Secant|Sheaf|Incidence|Ext2|PeriodTransport)",
    "primitive": r"(?:Primitive|Residual|Polariz|Lefschetz)",
    "worldtrace": r"(?:Worldtrace|GeneralSpace|SelfExpanding|Omniversal|GraphV2)",
    "cm_weil": r"(?:CM|Weil|Quaternion|Isogeny)",
    "target": r"(?:ExactClay|FullCorrespondence|AllHodge|UniversalHodge)",
}
indexed = []
counts = Counter()
backrefs = defaultdict(list)
for path in paths:
    file = ROOT / path
    raw = file.read_bytes()
    src = raw.decode("utf-8", "replace")
    lines = src.splitlines()
    imports = [m.group(1) for line in lines if (m := re.match(r"^\s*import\s+(\S+)", line))]
    decls = []
    for i, line in enumerate(lines, 1):
        m = declaration.match(line)
        if m:
            decls.append({"kind": m.group(1), "name": m.group(2), "line": i,
                          "header": line.strip()[:200]})
            if m.group(1) == "axiom":
                counts["axiom_declarations"] += 1
    # These counts are only a lexical audit; they require proof checking.
    sorry_lines = [i for i, line in enumerate(lines, 1)
                   if re.search(r"\b(?:sorry|admit|sorryAx)\b", line)
                   and not line.lstrip().startswith(("--", "/-", "*", "#print"))]
    source_score = (
        sum(5 for line in lines if re.search(r"\b(?:codimensionCycles|cycleClass|NativeMassCycleClassBridge)\b", line))
        + sum(3 for line in lines if re.search(r"\b(?:Hilbert|Semiregular|perfectComplex|SourceBirth)\b", line))
        + len(re.findall(r"\b(?:theorem|lemma)\b", src)) // 3
    )
    domain = [kind for kind, rx in tags.items()
              if re.search(rx, path) or re.search(rx, src[:2500])]
    for mod in imports:
        backrefs[mod].append(path)
    indexed.append({
        "path": path,
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "lines": len(lines),
        "imports": imports,
        "declarations": decls,
        "sorry_like_lines": sorry_lines,
        "domains": domain,
        "source_score": source_score
    })
    counts["lines"] += len(lines)
    counts["bytes"] += len(raw)
    counts["files"] += 1
    counts["declarations"] += len(decls)
    counts["sorry_like_lines"] += len(sorry_lines)

assert len(indexed) == len(paths)
out = ROOT / "gst_all_lean_source_inventory.json"
out.write_text(json.dumps({"head":subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip(),
                          "counts": dict(counts), "files": indexed}, indent=2), encoding="utf-8")
high = sorted(indexed, key=lambda x:x["source_score"], reverse=True)
suspect = [x for x in indexed if x["sorry_like_lines"] or any(d["kind"]=="axiom" for d in x["declarations"])]
top = sorted(((m,len(v)) for m,v in backrefs.items()),key=lambda x:x[1],reverse=True)[:35]
digest = ["# Entire Lean worktree — mechanical source map", "",
          "This index reads every tracked .lean file and records complete file hashes, imports and declaration headers.",
          "It does not establish kernel validity or that all theorems were manually audited.", "",
          f"**SHA:** {subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()}",
          f"**Files:** {counts['files']}; **lines:** {counts['lines']}; "
          f"**declarations:** {counts['declarations']}; **axioms:** {counts['axiom_declarations']}; "
          f"**sorry-like occurrences:** {counts['sorry_like_lines']}.",
          "", "## Top dependency imports", ""]
digest += [f"- {m}: {n} importers" for m,n in top]
digest += ["", "## High source-geometry weighted modules", ""]
digest += [f"- {x['path']}: {x['lines']} lines; {len(x['declarations'])} declarations; score {x['source_score']}" for x in high[:65]]
digest += ["", "## Lexically flagged axiom/hole files (not a proof verdict)", ""]
digest += [f"- {x['path']}: axiom {[d['name'] for d in x['declarations'] if d['kind']=='axiom']}; sorry-like lines {x['sorry_like_lines'][:12]}" for x in suspect[:65]]
digest += ["", "## Canonical whole-source output", "",
           "Use the JSON artifact for the complete 701-file inventory, every import edge, individual declaration heading and SHA-256.", ""]
(ROOT / "gst_all_lean_source_digest.md").write_text("\n".join(digest), encoding="utf-8")
print("FULL_LEAN_SOURCE_SCAN", json.dumps(dict(counts), sort_keys=True))
print("SCAN_SHA",subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT).decode().strip())
print("MOST_IMPORTED",json.dumps(top[:12]))
print("TOP_GEOMETRIC_MODULES",json.dumps([(x["path"],x["source_score"],x["lines"]) for x in high[:24]]))
print("AXIOM_HOLE_FILE_COUNT",len(suspect))
print("ACTUAL_CATALOG_RECORDED", len(indexed)==701)
