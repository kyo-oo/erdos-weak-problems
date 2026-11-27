def v2(x): return (x & -x).bit_length() - 1

def witness(M, t, h1):
    # memory-balanced: A over [0..h1-1], B over [h1..M]
    A = [(0, 0)]
    for i in range(h1): A = A + [(a + 3**i, m | (1 << i)) for a, m in A]
    B = [(0, 0)]
    for i in range(h1, M+1): B = B + [(b + 3**i, m | (1 << i)) for b, m in B]
    mod = 1 << t
    Ares = {}
    for a, m in A:
        r = a % mod
        if r not in Ares: Ares[r] = (a, m)
    for b, mb in B:
        r = (-b) % mod
        if r in Ares:
            a, ma = Ares[r]
            if a != 0 or b != 0:
                return ma | mb, a + b
    return None, None

import sys
M = int(sys.argv[1]); t = int(sys.argv[2]); h1 = int(sys.argv[3])
S, n = witness(M, t, h1)
if S is None:
    print(f"M={M} t={t}: NO WITNESS")
else:
    pos = [i for i in range(M+1) if (S >> i) & 1]
    val = sum(3**i for i in pos)
    print(f"M={M} t={t}: {len(pos)} digits | direct v2 = {v2(val)} | MITM-match: {val==n} | odd part: {(val >> t) % 2 == 1}")
