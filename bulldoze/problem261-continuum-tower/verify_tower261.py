import sys; sys.set_int_max_str_digits(200000)
from fractions import Fraction as F

# ============ 1. THE INFINITE EXACT-HALVING FAMILY ============
def m(k): return 2**(k+1) - k - 2
print("=== halving family {m_k} = {m_k+1..m_k+k} ===")
for k in range(1, 13):
    mk = m(k)
    lhs = F(mk, 2**mk)
    rhs = sum(F(mk+i, 2**(mk+i)) for i in range(1, k+1))
    assert lhs == rhs, f"FAIL k={k}"
    print(f"k={k:2d}  m_k={mk:5d}  value={lhs}  (float {float(lhs):.6g})  OK")

# ============ 2. REGION DISJOINTNESS ============
print("\n=== region disjointness [m_k, m_k+k] ===")
regs = [(m(k), m(k)+k) for k in range(1, 60)]
ok = all(regs[i][1] < regs[i+1][0] for i in range(len(regs)-1))
print("pairwise disjoint for k=1..59:", ok)
assert ok
gaps = [regs[i+1][0]-regs[i][1] for i in range(10)]
print("first gaps:", gaps)

# ============ 3. TOWER VALUE V = Σ m_k 2^{-m_k} (exact partials) ============
print("\n=== tower value V ===")
V = F(0)
for k in range(1, 13):
    V += F(m(k), 2**m(k))
print("V (k<=12) float:", float(V))
# tail bound: sum of terms k>12 < 2 * next term (superexponential decay)
nxt = F(m(13), 2**m(13))
print("next term (float):", float(nxt), " tail < 2*next:", float(nxt)*2)

# ============ 4. ALL C_T SUM TO THE SAME VALUE (finite-k check) ============
print("\n=== C_T invariance (gadget choices, k<=12) ===")
def C(T, K=12):
    s = F(0)
    for k in range(1, K+1):
        if k in T: s += F(m(k), 2**m(k))
        else: s += sum(F(m(k)+i, 2**(m(k)+i)) for i in range(1, k+1))
    return s
Ts = [set(), {1}, {2}, {3}, {1,2}, {2,5}, {1,3,5,7,9,11}, set(range(1,13))]
vals = [C(T) for T in Ts]
print("all equal:", all(v == vals[0] for v in vals), " value:", vals[0])
assert all(v == vals[0] for v in vals)

# ============ 5. V IS IRRATIONAL (cluster isolation, bit-level) ============
print("\n=== V irrationality evidence (binary clusters) ===")
# exact binary expansion of V to 600 bits using k<=12 (tail < 2^-4000)
num, den = V.numerator, V.denominator
bits = []
rem = num
D = den  # den = 2^M
M = D.bit_length()-1
for pos in range(1, 601):
    b = (num >> (M - pos)) & 1 if pos <= M else 0
    bits.append(b)
s = ''.join(map(str, bits))
# cluster positions m_k
for k in range(1, 9):
    print(f"m_{k}={m(k):4d}: bits around: ...{s[m(k)-6:m(k)+1]} | gap-after (zeros): ", end="")
    # count zeros after cluster
    j = m(k)
    z = 0
    while j+1 < len(s) and s[j] == '0': z += 1; j += 1
    print(z)

# ============ 6. KNOWN COLLISIONS RECHECK (Kill #5 witnesses) ============
print("\n=== known collisions recheck ===")
def S(A): return sum(F(a, 2**a) for a in A)
assert S([2]) == S([3,6,8]) == S([4,5,6]) == F(1,2)
assert S([4,5]) == S([3,8]) == F(13,32)
print("1/2 x3 reps OK; {4,5}={3,8}=13/32 OK")
print("\nALL TOWER CHECKS PASSED")
