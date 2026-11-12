import json, math
from math import gcd
fam = json.load(open('../fam5040.json'))
rows = []
for q, v in fam.items():
    h, U, V, o2, o3 = v
    rows.append((int(q), h, U, V, o2, o3))

def kernel_lattice(u, v, h):
    """basis of {(k,l) in Z^2 : u*k + v*l == 0 mod h}"""
    g0 = gcd(gcd(u, v), h)
    if g0 > 1:
        u //= g0; v //= g0; h //= g0
    g1 = gcd(u, v)
    if g1 == 0:
        return ((1, 0), (0, 1))
    old_r, r = u, v
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        qq = old_r // r
        old_r, r = r, old_r - qq * r
        old_s, s = s, old_s - qq * s
        old_t, t = t, old_t - qq * t
    if old_r < 0:
        old_s, old_t = -old_s, -old_t
    s, t = old_s, old_t
    gg = gcd(g1, h)
    m1 = h // gg
    a, bp = s, -(v // g1)
    c, dp = t, (u // g1)
    return (a * m1, c * m1), (bp, dp)

print("q      h    U    V   | o2  o3 | grp=|<2,3>|  latIdx  modpow(b1) modpow(b2) | g_v  m_l  g_u  m_k | h-factor")
ok_all = True
for (q, h, U, V, o2, o3) in sorted(rows, key=lambda r: r[1]):
    # 1) closure of <2,3> mod q
    S = set([1]); frontier=[1]
    while frontier:
        x = frontier.pop()
        for y in (x*2 % q, x*3 % q):
            if y not in S:
                S.add(y); frontier.append(y)
    grp_ok = (len(S) == h)
    # 2) orders
    o2c = next(i for i in range(1, q) if pow(2, i, q) == 1)
    o3c = next(i for i in range(1, q) if pow(3, i, q) == 1)
    ord_ok = (o2c == o2 and o3c == o3 and o2*o3//gcd(o2,o3) == h)
    # 3) kernel lattice basis satisfies 2^k 3^l == 1 mod q
    b1, b2 = kernel_lattice(U, V, h)
    det = abs(b1[0]*b2[1] - b1[1]*b2[0])
    def mp(k, l):
        a = pow(2, k, q) if k >= 0 else pow(pow(2, -k, q), -1, q)
        b = pow(3, l, q) if l >= 0 else pow(pow(3, -l, q), -1, q)
        return a*b % q
    lat_ok = (det == h) and mp(*b1) == 1 and mp(*b2) == 1
    g_v = gcd(V, h); m_l = h // g_v
    g_u = gcd(U, h); m_k = h // g_u
    # factor h
    f = {}
    x = h
    for p in (2,3,5,7):
        while x % p == 0: f[p] = f.get(p,0)+1; x //= p
    assert x == 1, (q, h)
    fs = "2^%d 3^%d 5^%d 7^%d" % (f.get(2,0), f.get(3,0), f.get(5,0), f.get(7,0))
    status = "OK" if (grp_ok and ord_ok and lat_ok) else "FAIL grp=%s ord=%s lat=%s" % (grp_ok, ord_ok, lat_ok)
    if status != "OK": ok_all = False
    print(f"{q:6d} {h:5d} {U:4d} {V:4d} | {o2:3d} {o3:3d} | {len(S):5d} {det:6d}  {mp(*b1):3d} {mp(*b2):3d} | {g_v:3d} {m_l:4d} {g_u:3d} {m_k:4d} | {fs:16s} {status}")
print()
print("ALL OK" if ok_all else "SOME FAILURES")
