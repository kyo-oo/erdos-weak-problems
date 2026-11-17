#!/usr/bin/env python3
"""Register the *actual* transitive local Lean import closure for a CI lane.

Lake's lean_lib roots must name local custom modules, including nested
imports, even when the requested entry file imports them in Lean source.
Use this generator instead of repairing one 'unknown module prefix' at a time.

Usage:
  python3 scripts/gst_lean_dependency_roots.py LIB ROOT [ROOT ...]
This writes one [[lean_lib]] declaration to the existing lakefile.toml.
No Lean or Mathlib installation is needed to compute the import closure.
"""
from pathlib import Path
import json
import re
import sys

IMPORT=re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
LOCAL_ROOT_PREFIXES=("GST","Hodge","CardinalWorlds","Monolith","Comparator")

def generate(lib: str, roots: list[str], project: Path = Path(".")):
    visited=set()
    in_progress=set()
    order=[]
    def visit(module: str):
        if module in visited:
            return
        if module in in_progress:
            raise ValueError(f"Cyclic local Lean import: {module}")
        local_path=project / (module.replace(".","/")+".lean")
        if not local_path.is_file():
            if module.startswith(LOCAL_ROOT_PREFIXES):
                raise FileNotFoundError(f"Missing local Lean module: {module} ({local_path})")
            return
        in_progress.add(module)
        data=local_path.read_text(encoding="utf-8")
        for line in data.splitlines():
            m=IMPORT.match(line)
            if not m:
                continue
            for token in m.group(1).split():
                visit(token)
        in_progress.remove(module)
        visited.add(module)
        order.append(module)
    for root in roots:
        visit(root)
    if not all(root in visited for root in roots):
        raise ValueError(f"Unregistered requested roots: {roots}")
    entry="\n[[lean_lib]]\nname = "+json.dumps(lib)+"\nroots = [\n"
    entry+="".join("  "+json.dumps(mod)+",\n" for mod in order)
    entry+="]\n"
    with (project/"lakefile.toml").open("a",encoding="utf-8") as f:
        f.write(entry)
    print(f"Registered {len(order)} local Lean modules for {lib}: "
          +", ".join(roots))
    return order

if __name__=="__main__":
    if len(sys.argv)<3:
        raise SystemExit("Usage: python3 gst_lean_dependency_roots.py LIB ROOT [ROOT ...]")
    generate(sys.argv[1],sys.argv[2:])
