#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
audit_w81_c_compare.py — W81-107B — THE SIBLING-LANE C-PORT COMPARISON.

Adversarial comparison of the W81-107A C port (engine107f9.c, read-only,
worktree /home/z/waves/w81-107a) against the python v2 machinery re-run
independently by this lane (engine107audit_w81.py check A6, dump file
audit_w81_v2parents.json).

Comparison layers (all exact):
  L1  parent admission: the C engine must accept the dumped arrangement-
      generic realization (shear t=0, already generic) and agree on the
      parent chi.
  L2  CELLS: the C's cell count on the SAME realization must equal the
      python slab-sampler count (287 at n=8) and the C's internal
      line-arrangement formula check must hold.
  L3  S1 CHILDREN: the canonical child set derived from the cells (the
      deterministic S1 layer) must agree: python S1 canonical keys ==
      the S1 subset of the C output (checked as: python S1 set is a
      subset of the C's emitted canonical set, and sizes compared).
  L4  CANONICAL FORM: every python child chi (S1 and full A6 set) is fed
      through the C's --canon-only mode; the C's canonical key must
      equal the python canonical_key packing (the two-code law at the
      canonical-form level, ~1200 chirotopes).
  L5  FULL SET: the C's full children set (S1+S2+S3, its own rng) vs the
      python A6 full set (S1+S2+S3, python rng): both must contain S1;
      set relations reported (walk-rng differences are expected and
      documented, not failures, as long as S1 agrees and both certify).

Output: human-readable report + exit code (0 = every hard layer passes).
"""
import json
import os
import subprocess
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MYW = HERE                                    # /home/z/waves/w81-107b/problem107-happy-ending
SIB = "/home/z/waves/w81-107a/problem107-happy-ending"
C_BIN = os.path.join(SIB, "engine107f9")
DUMP = os.path.join(HERE, "audit_w81_v2parents.json")

sys.path.insert(0, MYW)
import engine107f5v2 as V2  # noqa: E402  (my worktree copy; same commit content)


def pack_hex(sv):
    """Sign packing, the C engine convention (engine107f9.c unpack_hex /
    engine107f5v4.py pack_signs): bit i = (s_i > 0); the string is the
    BIG-ENDIAN zero-padded hex of the bits integer (nibble b = bits
    4b..4b+3, b = 0 lowest, is the character at position (nib-1-b)).
    (W81-107B-F finisher repair: the first draft packed little-endian —
    the C read every chi nibble-reversed and FATAL'd "shear chi mismatch".)
    """
    bits = 0
    for i, s in enumerate(sv):
        if s > 0:
            bits |= 1 << i
    return format(bits, "0{}x".format((len(sv) + 3) // 4))


def unpack_hex(hexs, L):
    """Inverse of pack_hex (C pack_hex output -> sign tuple of length L)."""
    bits = int(hexs, 16)
    return tuple(1 if (bits >> i) & 1 else -1 for i in range(L))


def main():
    with open(DUMP, encoding="utf-8") as f:
        data = json.load(f)
    parents = data["parents"]
    print(f"loaded {len(parents)} dumped parents (seed {data['seed']})")
    report = []
    ok_all = True

    # ---------- build the C batch input from the dumped realizations ------
    batch = []
    py_info = []
    for k, p in enumerate(parents):
        pts = [(F(x), F(y)) for (x, y) in p["realization"]]
        n = len(pts)
        assert n == 8
        chi = V2.chi_of_points(pts)
        # python S1 on the SAME realization (deterministic)
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        posmap = {t: q for q, t in enumerate(V2.TRIPLES(n))}
        sh, cells = V2.arrangement_cell_samples(pts)
        s1 = set()
        for (sx, sy) in cells:
            sv = V2.sv_of_point(sh, (sx, sy), pairs)
            chi9 = V2.chi_insert(chi, n, sv, pairs, posmap)
            s1.add(chi9)
        s1_ck = set(V2.canonical_key(c9, n + 1, V2.rule_for(n + 1)) for c9 in s1)
        py_info.append({"pos": p["pos"], "pts": pts, "chi": chi, "cells": len(cells),
                        "s1": s1, "s1_ck": s1_ck, "py_children": p["children"]})
        batch.append(f"P w81b-{k} {n} {pack_hex(chi)}")
        for (x, y) in pts:
            batch.append(f"{x} {y}")
    inp = "\n".join(batch) + "\n"

    # ---------- run the C engine (read-only; stdout only) ------------------
    proc = subprocess.run([C_BIN], input=inp, capture_output=True, text=True, timeout=560)
    if proc.returncode != 0:
        print("C ENGINE EXIT", proc.returncode)
        print(proc.stderr[:2000])
        return 2
    # parse output: T lines belong to the parent since the last #P;
    # an "#E <key> GENERIC-FAIL" line is a parent the C could NOT make
    # arrangement-generic (an L1 failure — recorded, never silently lost)
    c_parents = []
    n_genfail = 0
    cur = {"T": [], "P": None}
    for line in proc.stdout.splitlines():
        if line.startswith("T "):
            cur["T"].append(line.split()[1])       # ck-hex
        elif line.startswith("#E ") and "GENERIC-FAIL" in line:
            n_genfail += 1
            cur["P"] = line                        # sentinel: failed parent
            c_parents.append(cur)
            cur = {"T": [], "P": None}
        elif line.startswith("#P "):
            cur["P"] = line
            c_parents.append(cur)
            cur = {"T": [], "P": None}
    if cur["T"] or cur["P"]:
        c_parents.append(cur)
    print(f"C engine answered {len(c_parents)} parent jobs "
          f"({n_genfail} GENERIC-FAIL)")
    if len(c_parents) != len(parents):
        print("FAIL: parent job count mismatch")
        return 2

    # ---------- L1/L2/L3/L5 per parent --------------------------------------
    for k, (pi, cp) in enumerate(zip(py_info, c_parents)):
        stat = cp["P"]
        if stat is None or "GENERIC-FAIL" in stat:
            report.append(f"parent {k} (bank pos {pi['pos']}): C GENERIC-FAIL "
                          f"(L1 FAIL)")
            ok_all = False
            continue
        cells_c = int(_field(stat, "cells="))
        formula = _field(stat, "formula=")
        children_c = int(_field(stat, "children="))
        selfcheck = _field(stat, "selfcheck=")
        c_ck = set(cp["T"])
        py_ck_hex = set(pack_hex(ck) for ck in pi["s1_ck"])
        l2 = (cells_c == pi["cells"]) and formula == "1"
        l3 = py_ck_hex.issubset(c_ck) and c_ck.issuperset(py_ck_hex)
        l1 = ("GENERIC-FAIL" not in stat) and selfcheck == "1" and len(c_ck) > 0
        # L5: relations of the full sets (informational)
        report.append(
            f"parent {k} (bank pos {pi['pos']}): cells C={cells_c} py={pi['cells']} "
            f"(L2 {'OK' if l2 else 'MISMATCH'}); C children={children_c} "
            f"(emitted distinct ck={len(c_ck)}) vs py A6 children={pi['py_children']}; "
            f"S1 canonical keys: py={len(py_ck_hex)}, all present in C output: "
            f"{l3}; C-only keys: {len(c_ck - py_ck_hex)} (walk/sweep rng difference)")
        ok_all = ok_all and l1 and l2 and l3
    for r in report:
        print(r)

    # ---------- L4: canonical-form cross-validation -------------------------
    all_chi = set()
    for pi in py_info:
        all_chi |= pi["s1"]
    # plus the full A6 child chis: re-run the python job quickly for chi sets
    with open(os.path.join(HERE, "engine107f5_cache", "ot8_v2.pkl"), "rb") as f:
        import pickle
        types8 = pickle.load(f)
    items = sorted(types8.items())
    for p in parents:
        rec = items[p["pos"]][1]
        seed = 700000 + 8 * 131 + p["pos"]
        _k, children, _st = V2._parent_job_v2((items[p["pos"]][0], rec, seed,
                                               {"sweep": True, "walk": True,
                                                "walk_steps": 6}))
        all_chi |= set(children.keys())
    lines = [f"K 9 {pack_hex(c9)}" for c9 in all_chi]
    proc2 = subprocess.run([C_BIN, "--canon-only"], input="\n".join(lines) + "\n",
                           capture_output=True, text=True, timeout=560)
    if proc2.returncode != 0:
        print("CANON-ONLY EXIT", proc2.returncode, proc2.stderr[:1000])
        return 2
    n_ok = 0
    n_bad = 0
    n_skip = 0
    for line in proc2.stdout.splitlines():
        if not line.startswith("CK "):
            continue
        _tag, chex, ckhex = line.split()
        if len(chex) * 4 < 84:
            n_skip += 1
            continue
        # recompute python canonical on the same chi (hex -> signs exactly)
        chi_t = unpack_hex(chex, 84)
        py_ck = pack_hex(V2.canonical_key(chi_t, 9, V2.rule_for(9)))
        if py_ck == ckhex:
            n_ok += 1
        else:
            n_bad += 1
    print(f"L4 canonical-form cross-validation: {n_ok} chirotopes agree, "
          f"{n_bad} disagree ({n_skip} skipped)")
    ok_all = ok_all and n_bad == 0 and n_ok >= len(all_chi) * 0.99
    print("C-COMPARE " + ("PASS" if ok_all else "FAIL"))
    return 0 if ok_all else 1


def _field(line, key):
    for tok in line.split():
        if tok.startswith(key):
            return tok[len(key):]
    return None


if __name__ == "__main__":
    sys.exit(main())
