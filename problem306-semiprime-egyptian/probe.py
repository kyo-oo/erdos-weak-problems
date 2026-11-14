import time, sys
sys.setrecursionlimit(300000)
from engine306_w63 import (PRIMES, XS, WINS, DENS, solve_window, dfs_solve,
                           mitm_solve, window_items, verify_pair)
from fractions import Fraction
for (a,b) in [(9,10),(10,11),(12,13)]:
    print(f"--- {a}/{b} ---", flush=True)
    for xi,X in enumerate(XS):
        d = DENS[xi]
        if Fraction(a,b) > d: continue
        if X < 23: continue
        t0=time.time()
        got = solve_window(WINS[xi], a, b, set(), cap=6_000_000, tmo=25.0)
        dt = time.time()-t0
        if got and verify_pair(a,b,got):
            print(f"  X={X} ({len(WINS[xi])} pr): {len(got)} terms max {got[-1]} [{dt:.1f}s]", flush=True)
            break
        print(f"  X={X}: miss [{dt:.1f}s]", flush=True)
    else:
        print(f"  {a}/{b}: STILL FAIL", flush=True)
