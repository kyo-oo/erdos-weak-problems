import json, time, sys
from itertools import combinations

# THE DOUBTER FRONTIER PROBE (S094 council, mode B internal)
# Method 1 (third-method recompute, M <= 24): exact subset enumeration.
# Method 2 (extension, M >= 25): meet-in-the-middle on exact integer sums,
#   per-t residue-set membership: v2*(M) >= t iff exists (a in A, b in B): a+b == 0 mod 2^t.
# Also: primitive variant (S must contain 0 => n = 1 mod 3), and small-k frontier.

def v2(x):
    if x == 0: return 10**9
    return (x & -x).bit_length() - 1

def v2star_enum(M):
    best = 0; bestS = None
    powers = [3**i for i in range(M+1)]
    # enumerate all nonempty subsets via iterative mask
    for mask in range(1, 1 << (M+1)):
        s = 0
        # fast: use precomputed? M<=20 => 2^21 subsets, do incremental gray code
        pass
    # gray-code incremental for speed
    s = 0; prev = 0
    # gray code: g = mask ^ (mask>>1); track changes
    cur = 0
    best = 0
    for mask in range(1, 1 << (M+1)):
        g = mask ^ (mask >> 1)
        diff = g ^ prev
        if diff:
            b = diff.bit_length() - 1
            if g >> b & 1: cur += powers[b]
            else: cur -= powers[b]
        prev = g
        t = v2(cur)
        if t > best: best = t; bestS = g
    return best, bestS

def v2star_mitm(M, tmax=None, primitive=False):
    # split [0..M] into low = [0..h-1], high = [h..M]
    h = (M+1)//2
    low_p = [3**i for i in range(h)]
    high_p = [3**i for i in range(h, M+1)]
    A = set(); B = set()
    # enumerate subset sums of low (2^h) — h <= 22
    n_low = len(low_p)
    for mask in range(1 << n_low):
        s = 0
        # chunked enumeration via recursion-free accumulation:
        # use the standard trick: iterate and add via bit tricks — for h<=22, 4M masks, keep it simple
        mm = mask; idx = 0; s = 0
        while mm:
            lb = mm & -mm
            s += low_p[lb.bit_length()-1]
            mm ^= lb
        A.add(s)
        if primitive and (mask & 1):
            pass  # primitive handled separately below
    n_high = len(high_p)
    for mask in range(1 << n_high):
        mm = mask; s = 0
        while mm:
            lb = mm & -mm
            s += high_p[lb.bit_length()-1]
            mm ^= lb
        B.add(s)
    if primitive:
        # S contains 0: A restricted to masks with bit0 = 1 -> subtract 1: sums = 1 + (subset of low[1:])
        A = set()
        for mask in range(1 << (n_low-1)):
            mm = mask; s = 1
            while mm:
                lb = mm & -mm
                s += low_p[1 + lb.bit_length()-1]
                mm ^= lb
            A.add(s)
    # find max t with a+b == 0 mod 2^t, (a,b) not both "empty" — note a=0 (empty low) allowed only if b != 0
    if tmax is None: tmax = M + 14
    A_list = sorted(A)
    B_list = sorted(B)
    best = 0
    for t in range(1, tmax+1):
        mod = 1 << t
        Amod = set(a % mod for a in A_list)
        # need any b: (-b) % mod in Amod, with not(a==0 and b==0)
        found = False
        Bmod = set()
        # quick screen: collect b mod
        for b in B_list:
            r = (-b) % mod
            if r in Amod:
                # verify not both empty: a with a%mod==r exists with (b!=0 or a!=0)
                found = True; break
        if not found: break
        best = t
    return best

results = {}
t0 = time.time()
# Method 1: exact enumeration M=0..20 (gray code)
for M in range(0, 21):
    best, S = v2star_enum(M)
    results[M] = {'v2star': best, 'method': 'enum'}
print("enum done M<=20", time.time()-t0, file=sys.stderr)

# Method 2: MITM M=21..42
for M in range(21, 43):
    t1 = time.time()
    best = v2star_mitm(M)
    results[M] = {'v2star': best, 'method': 'mitm'}
    print(f"M={M} v2*={best} ({time.time()-t1:.0f}s)", file=sys.stderr, flush=True)

json.dump(results, open('S094_v2star_recomputed.json','w'), indent=1)
print(json.dumps({m: r['v2star'] for m, r in results.items()}))
