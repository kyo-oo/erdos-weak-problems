def digits3(n):
    ds = []
    while n > 0:
        ds.append(n % 3)
        n //= 3
    return ds

def walk(K, maxp=None):
    # digits of 4^K
    R = 4**K
    ds = digits3(R)  # ds[p] = digit p
    if maxp is None: maxp = len(ds)+1
    # carry walk: C(p) = (4*(R mod 3^p))/3^p
    res = []
    m = 1
    rm = R % 1
    for p in range(0, maxp):
        m3 = 3**(p+1)
        rm = R % m3
        C = (4*rm)//(3**p)
        d = ds[p] if p < len(ds) else 0
        res.append((p, d, C))
    return res, len(ds)

for K in [5, 6, 7, 8, 9, 10, 13, 16, 17, 26]:
    w, top = walk(K)
    gates = [(p,d,C) for (p,d,C) in w if d==2 and C%3==0 and p>=1]
    print(f"K={K} (top digit pos {top-1}), first gate at p={gates[0][0] if gates else None}")
    if K in (5, 7, 9, 13):
        print("   walk (p, digit, carry):", w[:top+2])
