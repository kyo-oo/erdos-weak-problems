#!/usr/bin/env python3
"""w66_frames.py — THE FRAME TABLE (mission 2): budgets + torus sizes for the
symmetric tori (h | L), the ASYMMETRIC tori (o2 | L2, o3 | L3 — different
moduli on the k and l axes), and the pure dyadic-triadic tori (2^K, 3^J).
Palette = bank + deep scan (w66_deep.json)."""
import json, math, os

HERE = os.path.dirname(os.path.abspath(__file__))
pal = {int(k): v for k, v in json.load(open(os.path.join(HERE, "w66_deep.json"))).items()}

def frame_sym(L):
    rows = [r for r in pal.values() if L % r[3] == 0]
    return rows, sum(1.0 / r[3] for r in rows), L * L

def frame_asym(L2, L3):
    rows = [r for r in pal.values() if L2 % r[1] == 0 and L3 % r[2] == 0]
    return rows, sum(1.0 / r[3] for r in rows), L2 * L3

def frame_dyadic(K, J):
    return frame_asym(2 ** K, 3 ** J)

print("=" * 100)
print("SYMMETRIC TORI (family: h | L):")
for L in (27720, 55440, 110880, 166320, 831600, 720720, 1441440, 2162160, 4324320, 8648640, 12252240):
    rows, b, cells = frame_sym(L)
    print(f"  L={L:9d} fam={len(rows):4d} budget={b:.4f} torus={cells:.2e}  top: "
          + " ".join(f"{r[0]}:{r[3]}" for r in sorted(rows, key=lambda r: -1.0/r[3])[:8]))

print("=" * 100)
print("ASYMMETRIC TORI (family: o2 | L2, o3 | L3):")
ASYM = [(55440, 55440), (720720, 55440), (720720, 720720), (2162160, 55440), (2162160, 720720),
        (12252240, 55440), (12252240, 720720), (4324320, 55440), (4324320, 720720),
        (8648640, 720720), (8648640, 55440), (6126120, 720720), (12252240, 166320),
        (2162160, 166320), (2162160, 110880), (12252240, 8648640//4)]
res = {}
for (L2, L3) in ASYM:
    rows, b, cells = frame_asym(L2, L3)
    res[(L2, L3)] = (len(rows), b, cells)
    print(f"  ({L2:9d},{L3:8d}) fam={len(rows):4d} budget={b:.4f} torus={cells:.3e} cells "
          f"(cols=L3={L3}, rowbits=L2={L2})")

print("=" * 100)
print("DYADIC-TRIADIC TORI (L2=2^K, L3=3^J):")
for K in range(4, 11):
    line = []
    for J in range(3, 8):
        rows, b, cells = frame_dyadic(K, J)
        line.append(f"J={J}: fam={len(rows):3d} b={b:.4f}")
    print(f"  K={K:2d}: " + "  ".join(line))

print("=" * 100)
print("THE GLOBAL CEILING: total budget over the whole deep palette = "
      f"{sum(1.0/r[3] for r in pal.values()):.4f} over {len(pal)} primes")
json.dump({f"{k[0]},{k[1]}": v for k, v in res.items()}, open(os.path.join(HERE, "w66_frames.json"), "w"))
