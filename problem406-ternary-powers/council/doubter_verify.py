import json, time

def v2(x):
    if x == 0: return 1 << 30
    return (x & -x).bit_length() - 1

# METHOD INDEPENDENT VERIFICATION: recover the M=37 excess-10 witness by brute
# reconstruction (MITM with witness tracking), evaluate directly, and re-derive
# by a second split point.
def v2star_witness(M, t):
    # find a witness subset S ⊆ [0..M] with sum ≡ 0 mod 2^t, nonempty; or None
    h1 = (M + 1) // 2
    low = [3**i for i in range(h1)]
    high = [3**i for i in range(h1, M+1)]
    # A: (sum, mask) for low half
    A = [(0, 0)]
    for idx, p in enumerate(low):
        A = A + [(a + p, m | (1 << idx)) for a, m in A]
    B = [(0, 0)]
    for idx, p in enumerate(high):
        B = B + [(b + p, m | (1 << (h1 + idx))) for b, m in B]
    mod = 1 << t
    # map from residue -> (a, mask) ; prefer any
    from collections import defaultdict
    Amap = defaultdict(list)
    for a, m in A: Amap[a % mod].append((a, m))
    for b, mb in B:
        r = (-b) % mod
        if r in Amap:
            for a, ma in Amap[r]:
                if a != 0 or b != 0:
                    S = ma | mb
                    return S, a + b
    return None

# verify M=37, t=47 (the claimed excess +10)
S, n = v2star_witness(37, 47)
positions = [i for i in range(38) if (S >> i) & 1]
val = sum(3**i for i in positions)
print("M=37 t=47 witness positions:", positions)
print("direct evaluation: sum =", val)
print("v2(sum) =", v2(val), "| claimed >= 47 | sum == MITM value:", val == n)
print("sum // 2^47 =", val >> 47, "(must be odd:", (val >> 47) % 2 == 1, ")")
print("log3(sum) ~", val.bit_length() * 0.6931 / 1.0986)
# SECOND method check: t=48 must FAIL (exactness of the jump)
w48 = v2star_witness(37, 48)
print("t=48 witness exists:", w48 is not None)
