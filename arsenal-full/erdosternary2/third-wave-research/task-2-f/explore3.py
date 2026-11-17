def d(p, x):  # digit p of 4^x
    return (4**x // (3**p)) % 3

# verify top-trit law: d(p,x) = (d(p, x mod 3^(p-1)) + trit_{p-1}(x)) mod 3, p>=2
ok = True
for p in range(2, 8):
    M = 3**(p-1)
    for x in range(0, 3**p):
        r = x % M
        t = (x // M) % 3
        if d(p, x) % 3 != (d(p, r) + t) % 3:
            ok = False
            print("top-trit law FAILS", p, x, d(p,x), (d(p,r)+t)%3)
            break
    if not ok: break
print("top-trit law:", ok)

# Also verify d(1,x) = x mod 3
ok2 = all(d(1,x) == x % 3 for x in range(0, 20))
print("d(1,x) = x mod 3:", ok2)

# For each K, find first p and analyze the mechanism
def firstp(K):
    for p in range(1, 2*K+3):
        if d(p, K) == 2 and d(p, K+1) == 2:
            return p
    return None

# trits of K
def trits(n):
    ts = []
    while n > 0:
        ts.append(n % 3)
        n //= 3
    return ts

for K in list(range(5, 40)) + [100, 101, 242, 243, 244, 500, 501, 728, 729, 730, 1000]:
    p = firstp(K)
    print(f"K={K:5d} trits={trits(K)} v3={0 if K%3 else None} first_p={p}")
