#!/usr/bin/env python3
# Independent verification layer for hunt850: sympy.factorint cross-checks of
# (1) random rad samples, (2) all recorded length-2 pairs, (3) any length-3 witness.
import sys, os
from sympy import factorint

OUT = sys.argv[1] if len(sys.argv) > 1 else "."
rep = []

def rad(n):
    r = 1
    for p in factorint(n):
        r *= p
    return r

def fmt(n):
    f = factorint(n)
    return " * ".join((("%d^%d" % (p, e)) if e > 1 else str(p)) for p, e in sorted(f.items()))

# 1) sample radical cross-check (C SPF-walk vs sympy.factorint)
ok = bad = 0
for line in open(os.path.join(OUT, "sample_rads.txt")):
    n, r = map(int, line.split())
    if rad(n) == r:
        ok += 1
    else:
        bad += 1
        rep.append("SAMPLE MISMATCH: n=%d C=%d sympy=%d" % (n, r, rad(n)))
rep.append("sample rad cross-check (C SPF-walk vs sympy.factorint, 64 random n in [1,N]): %d OK / %d MISMATCH" % (ok, bad))

# 2) length-2 pairs: full sympy re-verification
pairs = []
p2 = os.path.join(OUT, "length2_pairs.txt")
if os.path.exists(p2):
    pairs = [tuple(map(int, l.split())) for l in open(p2) if l.strip()]
bad2 = 0
for (x, y, r0, r1) in pairs:
    if not (x < y and rad(x) == rad(y) == r0 and rad(x + 1) == rad(y + 1) == r1):
        bad2 += 1
        rep.append("L2 MISMATCH: (%d,%d)" % (x, y))
rep.append("length-2 pairs re-verified with sympy.factorint: %d pairs total, %d bad" % (len(pairs), bad2))

# 3) length-3 witness (if any)
p3 = os.path.join(OUT, "witness_details.txt")
if os.path.exists(p3) and os.path.getsize(p3) > 0:
    x = y = None
    for line in open(p3):
        if line.startswith("PAIR"):
            _, x, y = line.split()
            x, y = int(x), int(y)
    if x is not None:
        rep.append("WITNESS: x=%d y=%d" % (x, y))
        for tag, n in [("x", x), ("x+1", x + 1), ("x+2", x + 2), ("y", y), ("y+1", y + 1), ("y+2", y + 2)]:
            rep.append("  %-4s = %d = %-40s rad = %d" % (tag, n, fmt(n), rad(n)))
        rx = [rad(x), rad(x + 1), rad(x + 2)]
        ry = [rad(y), rad(y + 1), rad(y + 2)]
        verdict = (x != y) and rx == ry
        rep.append("  rad triple x: %s" % rx)
        rep.append("  rad triple y: %s" % ry)
        rep.append("  SYMPY VERIFICATION: %s" %
                   ("PASS — length-3 Erdos-Woods witness CONFIRMED" if verdict else "FAIL"))
else:
    rep.append("witness_details.txt: absent/empty — no length-3 witness found (consistent with hunt verdict)")

# 4) length-2 summary (bonus evidence)
if pairs:
    beyond = [(x, y) for (x, y, r0, r1) in pairs if x > 20000]
    rep.append("length-2 summary: total %d; with smaller member > 2*10^4: %d" % (len(pairs), len(beyond)))
    for x, y in beyond[:40]:
        rep.append("  beyond-2e4 L2 pair: (%d, %d)" % (x, y))

txt = "\n".join(rep) + "\n"
print(txt)
open(os.path.join(OUT, "verification.txt"), "w").write(txt)
