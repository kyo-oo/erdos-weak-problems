"""Method A run: forward residue-DP big-int bitset sweep, t in [1, T_A]."""
import sys, json, time
sys.path.insert(0, "/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter")
from lib import methodA_sweep

T_A = int(sys.argv[1]) if len(sys.argv) > 1 else 31
M_MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 31
OUT = "/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter/methodA.json"

t0 = time.perf_counter()
flags = None
try:
    flags = methodA_sweep(T_A, M_MAX, verbose=True)
except MemoryError:
    # retry without the top t (halves the bitset)
    T_A -= 1
    print(f"[methodA] MemoryError at top t; retrying with T_A={T_A}", flush=True)
    flags = methodA_sweep(T_A, M_MAX, verbose=True)

v2star_A = {}
for M in range(M_MAX + 1):
    ts = [t for t in range(1, T_A + 1) if flags[t][M]]
    v2star_A[M] = max(ts) if ts else 0
    # if the top t still matches, the value is only bracketed from below
    if flags[T_A][M]:
        v2star_A[M] = {"ge": T_A, "note": f"match at t={T_A}; exact value needs higher t"}

json.dump({
    "method": "forward residue DP, Python big-int bitsets (circular shift by 3^i mod 2^t), one pass per t over all M",
    "T_A": T_A, "M_MAX": M_MAX,
    "wall_sec": round(time.perf_counter() - t0, 1),
    "match_top_row": flags[T_A],
    "v2star_methodA": v2star_A,
}, open(OUT, "w"), indent=1)
print("wrote", OUT)
print({M: (v if isinstance(v, int) else v["ge"]) for M, v in v2star_A.items()})
