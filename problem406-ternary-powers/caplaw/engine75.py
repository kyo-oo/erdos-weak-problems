# KERNEL 75 ENGINE — the depth-100 extension: W100, the three π-points at 3^100,
# trit receipts, size receipts. DUAL-METHOD: (A) cMod recursion vs (B) direct
# modular division (4^(3^s) mod 3^(s+101)); (C) Hensel lift vs (D) pow-inverse.
import sys

# ---------- Method A: the cMod recursion ----------
def cmod(k, stop):
    """cMod k s for s=0..stop; returns list."""
    m = 3**k
    cs = [1 % m]
    c = cs[0]
    for s in range(stop):
        c = (c + 3**(s+1)*c*c + 3**(2*s+1)*c**3) % m
        cs.append(c)
    return cs

D = 100
M = 3**D
csA = cmod(D, 99)
W100_A = csA[99]

# ---------- Method B: direct modular division ----------
def tower_coeff_mod(s, k):
    """c_s mod 3^k via 4^(3^s) mod 3^(k+s+1)."""
    m = 3**(k + s + 1)
    p = pow(4, 3**s, m)
    assert (p - 1) % 3**(s+1) == 0
    return ((p - 1) // 3**(s+1)) % 3**k

W100_B = tower_coeff_mod(99, 100)
assert W100_A == W100_B, "W100 DUAL METHOD MISMATCH"
print("W100 dual-verified:", W100_A)
print("W100 % 9 =", W100_A % 9, "| % 27 =", W100_A % 27, "| % 3 =", W100_A % 3)

# crosscheck depth 61 against the kernel's published W61
cs61 = cmod(61, 60)
W61_kernel = 60776643992856088575557123854
assert cs61[60] == W61_kernel, "W61 crosscheck FAILED"
print("W61 crosscheck vs kernel constant: OK")

# ---------- the π-points at depth 100 ----------
# 2*W*pi + T ≡ 0 (mod 3^100), T: fam4(head1)=7, fam7(head4)=1, fam1(head7)=3^100-5
def solve_pi(W, T, M):
    return (-T) * pow(2*W % M, -1, M) % M

pi_fam4 = solve_pi(W100_A, 7, M)
pi_fam7 = solve_pi(W100_A, 1, M)
pi_fam1 = solve_pi(W100_A, M - 5, M)

# Method C: Hensel lift trit by trit (independent)
def hensel_pi(W, T, depth):
    """solve 2W x + T ≡ 0 mod 3^depth by lifting one trit at a time."""
    x = 0
    for d in range(1, depth+1):
        m = 3**d
        # find trit t in {0,1,2} with 2W(x+t*3^(d-1)) + T ≡ 0 mod 3^d
        for t in range(3):
            cand = x + t * 3**(d-1)
            if (2*W*cand + T) % m == 0:
                x = cand
                break
        else:
            raise RuntimeError("hensel fail at depth %d" % d)
    return x

assert hensel_pi(W100_A, 7, 100) == pi_fam4, "pi_fam4 DUAL MISMATCH"
assert hensel_pi(W100_A, 1, 100) == pi_fam7, "pi_fam7 DUAL MISMATCH"
assert hensel_pi(W100_A, M - 5, 100) == pi_fam1, "pi_fam1 DUAL MISMATCH"
print("pi DUAL-VERIFIED (pow-inverse == Hensel)")

# receipts
assert (2*W100_A*pi_fam4 + 7) % M == 0
assert (2*W100_A*pi_fam7 + 1) % M == 0
assert (2*W100_A*pi_fam1 + (M-5)) % M == 0

# crosscheck vs kernel 61-trit constants
assert pi_fam4 % 3**61 == 68350949682967876566738142093, "pi_fam4 61-crosscheck FAILED"
assert pi_fam7 % 3**61 == 64267339165701958313626862986, "pi_fam7 61-crosscheck FAILED"
assert pi_fam1 % 3**61 == 60183728648436040060515583879, "pi_fam1 61-crosscheck FAILED"
print("all three pi 61-trit crosschecks vs kernel constants: OK")

# head checks (head = 7*pi % 9): fam4->head1, fam7->head4, fam1->head7
assert 7*pi_fam4 % 9 == 1 and 7*pi_fam7 % 9 == 4 and 7*pi_fam1 % 9 == 7
assert pi_fam4 % 3 == 1 and pi_fam7 % 3 == 1 and pi_fam1 % 3 == 1
print("head + rider-core (pi%3==1) checks: OK")

# ---------- trits ----------
def trits(n, depth):
    t = []
    x = n
    for _ in range(depth):
        t.append(x % 3)
        x //= 3
    return t

for name, pi in [("fam4", pi_fam4), ("fam7", pi_fam7), ("fam1", pi_fam1)]:
    t = trits(pi, 100)
    deep_twos = [i for i in range(61, 100) if t[i] == 2]
    all_twos = [i for i in range(100) if t[i] == 2]
    lead = max(i for i in range(100) if t[i] != 0)
    print(f"pi_{name}: {pi}")
    print(f"  2-trits 61..99: {deep_twos}")
    print(f"  total 2-trits <100: {len(all_twos)} | leading trit at {lead}")
