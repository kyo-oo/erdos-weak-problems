import time
from z3 import Bool, Solver, Or, Not, And, Sum, If, sat, unsat, unknown, is_true

def aps3(N):
    out = []
    for a in range(0, N):
        for d in range(1, N):
            if a + 2*d >= N: break
            out.append((a, a+d, a+2*d))
    return out

def z3_query(N, target, fix0=True, timeout_ms=600000):
    x = [Bool(f"x{i}") for i in range(N)]
    s = Solver()
    s.set("timeout", timeout_ms)
    for ap in aps3(N):
        s.add(Or([Not(x[v]) for v in ap]))
    s.add(Sum([If(x[i], 1, 0) for i in range(N)]) >= target)
    if fix0:
        s.add(x[0] == True)  # translation symmetry: WLOG 0 in A
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    wit = None
    if r == sat:
        m = s.model()
        wit = [i for i in range(N) if is_true(m[x[i]])]
    return r, wit, dt

if __name__ == "__main__":
    import sys
    N = int(sys.argv[1]); t = int(sys.argv[2])
    fix0 = (len(sys.argv) < 4 or sys.argv[3] != "nofix")
    r, wit, dt = z3_query(N, t, fix0)
    print(f"N={N} target={t} fix0={fix0} -> {r} in {dt:.1f}s", flush=True)
    if wit is not None:
        print("witness(0-based):", wit, flush=True)
