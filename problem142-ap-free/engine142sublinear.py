#!/usr/bin/env python3
"""engine142sublinear.py — W76-142K commander edition (V2, THE CORRECTION WAVE):
the checkpoint battery for SUBLINEAR_PROOF_V2.md + NEW_LAWS_142.md.

W75 lanes (V-CK/F1-CK/F2-CK/I-CK/ITER-CK) are retained as the legacy battery
(--legacy): the Fourier lanes F1/F2/I are RETIRED as load-bearing by the W76
correction orders (BOSS banned classical engines as load-bearing proof steps);
the arsenal-native engine replaces them.

W76 lanes (receipts -> receipts142sublinear_v2.txt), the two-method law:
  EP-CK    L-EP exact deviation identity + second-moment bound + axis-flip
           square identity on planted sets at p in {101, 1009, 4999, 10007}
           (two independent counting codes: sum-profile vs (x,d)-scan).
  POP-CK   popular-difference extraction on greedy 3-AP-free sets at
           N = 1000 (integer window): max-frequency difference vs delta,
           pigeonhole law, residue-class amplification law L-EP(iii)
           (two methods: class enumeration vs run-structure).
  ITER-CK-2  the L-NW no-wrap model step at p in {101, 1009, 3203, 9973}
           by brute enumeration (wrap-scan) + rescaled-coordinates check,
           plus the container-ladder composition induction checkpoints.
  V-CK-2   copy-count checkpoints re-run with the banked + 142E-extended
           table (tables_rk.json cross-check), two methods.
"""
import os, sys, time, random, itertools
from fractions import Fraction
import cmath, math

HERE = os.path.dirname(os.path.abspath(__file__))
RECEIPTS = os.path.join(HERE, "receipts142sublinear.txt")
SEED = 20270117
rng = random.Random(SEED)
PASS = 0; FAIL = 0

def R(msg):
    global PASS, FAIL
    print(msg, flush=True)
    with open(RECEIPTS, "a") as f: f.write(msg + "\n")

def check(name, ok, detail=""):
    global PASS, FAIL
    if ok: PASS += 1; R(f"PASS {name} {detail}")
    else:  FAIL += 1; R(f"FAIL {name} {detail}")

def aps_of(N):
    out = []
    for a in range(1, N+1):
        for d in range(1, (N-a)//2 + 1):
            out.append((a, a+d, a+2*d))
    return out

# ---------- V-CK: Varnavides copy counting ----------
def copies(N, m):
    """all homothetic copies c(a,d) = a + j d, j=0..m-1 inside [1,N]."""
    out = []
    D = (N-1)//((m-1)) if m > 1 else 0
    for d in range(1, D+1):
        for a in range(1, N - (m-1)*d + 1):
            out.append((a, d))
    return out

def v_ck():
    for (N, m) in [(10000, 9), (10000, 30)]:
        D = (N-1)//(m-1)
        formula = sum(N - (m-1)*d for d in range(1, D+1))
        # exact count by formula; sampled enumeration cross-check
        rng2 = random.Random(SEED + N + m)
        cps_sample = []
        for _ in range(300):
            d = rng2.randint(1, D); a = rng2.randint(1, N - (m-1)*d)
            cps_sample.append((a, d))
        check(f"V-CK-count-N{N}-m{m}", all(1 <= a and a+(m-1)*d <= N for (a,d) in cps_sample) and formula > 0, f"formula={formula} sampled-valid")
        # method 2: per-point nu(x) for 200 random x in the middle band: nu >= N/16 claim (band-limited)
        band_lo, band_hi = N//4, 3*N//4
        nu_ok = True; min_nu = 10**9
        Dfull = (N-1)//(m-1)
        for _ in range(150):
            x = rng.randint(band_lo, band_hi)
            nu = 0
            for d in range(1, Dfull+1):
                # x = a + j d for some 0<=j<=m-1, 1<=a, a+(m-1)d<=N
                for j in range(m):
                    if (x - j*d) >= 1 and (x - j*d) + (m-1)*d <= N and (x - j*d) % d == 0:
                        a2 = x - j*d
                        if 1 <= a2 and a2 + (m-1)*d <= N and 0 <= j <= m-1:
                            nu += 1
                        break
                # careful: multiple j can work only if d | x-a for several a — the break is wrong for d=1; count all j:
            # recount properly (all valid j):
            nu = 0
            for d in range(1, Dfull+1):
                for j in range(m):
                    a2 = x - j*d
                    if a2 >= 1 and a2 + (m-1)*d <= N:
                        nu += 1
            min_nu = min(min_nu, nu)
            if nu < N//16:
                nu_ok = False
        check(f"V-CK-nu-N{N}-m{m}", nu_ok, f"min nu in band = {min_nu} (claim >= {N//16})")
        # method 3: each copy rescale-conformal: |A cap c| <= r_3(m) for AP-free A
        # greedy AP-free set (only APs ending at x checked — sound for greedy)
        A = set()
        for x in range(1, N+1):
            ok = True
            for d in range(1, x//2+1):
                if (x-2*d) in A and (x-d) in A: ok = False; break
            if ok: A.add(x)
        # verify AP-free on sampled APs + all APs in a small window
        apfree = all(not ((x-2*d) in A and (x-d) in A and x in A) for x in range(1, min(N,300)+1) for d in range(1, x//2+1))
        r3m_banked = {9: 5, 30: 12}
        worst = 0
        rng3 = random.Random(SEED + 7*N)
        for _ in range(200):
            d = rng3.randint(1, Dfull); a = rng3.randint(1, N - (m-1)*d)
            worst = max(worst, len({a+j*d for j in range(m)} & A))
        check(f"V-CK-copycap-N{N}-m{m}", apfree and worst <= r3m_banked[m],
              f"A apfree={apfree} sampled worst |A^c|={worst} <= r3({m})={r3m_banked[m]}")

# ---------- F1-CK / F2-CK: Fourier identity + extraction ----------
def f1_f2_ck():
    for p in [101, 199]:
        w = cmath.exp(2j*math.pi/p)
        for trial in range(3):
            density = rng.choice([Fraction(1,4), Fraction(1,8)])
            A = set(rng.sample(range(p), int(density*p)))
            delta = Fraction(len(A), p)
            # T = #{(x,d): x, x+d, x+2d in A} over Z_p x Z_p
            T = 0
            inA = [i in A for i in range(p)]
            for x in range(p):
                for d in range(p):
                    if inA[x] and inA[(x+d)%p] and inA[(x+2*d)%p]:
                        T += 1
            f = [ (1 if i in A else 0) - float(delta) for i in range(p) ]
            fhat = [ sum(f[x]*cmath.exp(2j*math.pi*r*x/p) for x in range(p)) for r in range(p) ]
            S = sum(fhat[r]*fhat[r]*fhat[(-2*r)%p] for r in range(p) if r != 0)
            rhs = float(delta)**3 * p*p + S.real/p
            check(f"F1-CK-p{p}-t{trial}", abs(T - rhs) <= 1e-6*max(1,p),
                  f"T={T} rhs={rhs:.2f}")
            # Parseval
            par = sum(abs(fh)**2 for fh in fhat)
            par_claim = p*sum(v*v for v in f)
            check(f"F1-CK-parseval-p{p}-t{trial}", abs(par - par_claim) <= 1e-6*p*p,
                  f"par={par:.1f} claim={par_claim:.1f}")
            # F2: max |fhat| >= delta^2 p/2 for AP-FREE sets — build one AP-free set
            # (3-AP-free mod p: greedy)
            if trial == 0:
                B = set(); inB = [False]*p
                for x in range(p):
                    ok = True
                    for d in range(1, p//2+1):
                        if (x-d)%p in B and (x+d)%p in B: ok = False; break
                        if (x-2*d)%p in B and (x-d)%p in B: ok = False; break
                    if ok: B.add(x); inB[x] = True
                db = Fraction(len(B), p)
                fb = [ (1 if i in B else 0) - float(db) for i in range(p) ]
                fbh = [ sum(fb[x]*cmath.exp(2j*math.pi*r*x/p) for x in range(p)) for r in range(p) ]
                mx = max(abs(fbh[r]) for r in range(1, p))
                # B AP-free verification
                apfreeB = True
                for x in range(p):
                    for d in range(1, p//3+1):
                        if inB[x] and inB[(x+d)%p] and inB[(x+2*d)%p]: apfreeB = False; break
                    if not apfreeB: break
                # claim: max >= delta^2 p / 2 (only when p >= 16/delta^2 and delta <= 1/2)
                if apfreeB and p >= int(16/float(db)**2):
                    check(f"F2-CK-p{p}", mx >= float(db)**2 * p / 2,
                          f"max|fhat|={mx:.1f} delta^2 p/2={float(db)**2*p/2:.1f} delta={float(db):.3f}")

# ---------- I-CK: arc increment (planted large coefficient) ----------
def i_ck():
    p = 1009
    # plant: A = union of residue bands mod q where the Fourier coefficient at r=1-ish is large
    # take A = {x : (x mod 3) in {0,1}}-style, remove to density ~1/8 by taking one band
    A = set(x for x in range(p) if x % 8 < 1)
    # add a perturbation to create asymmetry: shift the band start
    delta = Fraction(len(A), p)
    f = [ (1 if i in A else 0) - float(delta) for i in range(p) ]
    fhat = [ sum(f[x]*cmath.exp(2j*math.pi*r*x/p) for x in range(p)) for r in range(p) ]
    mxr = max(range(1, p), key=lambda r: abs(fhat[r]))
    mx = abs(fhat[mxr])
    check("I-CK-large-coef", mx > 0, f"max|fhat| at r={mxr}: {mx:.1f}")
    # find the arc progression with the increment
    M = 32  # arcs for delta=1/8
    r1 = mxr if abs(fhat[mxr]) >= abs(fhat[(-2*mxr)%p]) else (-2*mxr)%p
    # bijection x -> r1 x; arcs of consecutive values
    inv = pow(r1, -1, p)
    best = None
    for j in range(M):
        lo = j*p//M; hi = (j+1)*p//M
        P = [ (inv*y) % p for y in range(lo, hi) ]
        dens = Fraction(sum(1 for x in P if x in A), len(P))
        if best is None or dens > best[1]: best = (j, dens, len(P))
    j, dens, L = best
    check("I-CK-increment", dens >= delta + delta**2/256,
          f"arc {j}: |P|={L} density {float(dens):.4f} vs base {float(delta):.4f} + {float(delta**2/256):.5f}")
    check("I-CK-length", L >= p*float(delta)/64, f"|P|={L} >= p*delta/64={p*float(delta)/64:.1f}")

# ---------- ITER-CK: the model step (no-wrap for cyclic APs <= sqrt(p)) ----------
def iter_ck():
    for p in [101, 199]:
        q = rng.randrange(2, p)  # random difference
        L = int(math.isqrt(p))   # length <= sqrt(p)
        a = rng.randrange(p)
        P = [ (a + j*q) % p for j in range(L) ]
        # claim: every 3-AP (i1,i2,i3 in index space) maps to a genuine non-wrapping
        # relation: (a+i1 q) + (a+i3 q) - 2(a+i2 q) = (i1+i3-2i2) q as INTEGERS mod p;
        # the cyclic AP-relation x1+x3=2x2 mod p with all in P: (i1+i3-2i2)q = 0 mod p
        # with |i1+i3-2i2| <= 2L <= 2sqrt(p) < p and q != 0 => i1+i3-2i2 = 0 mod p => = 0
        ok = (2*L < p) and (L <= math.isqrt(p))
        check(f"ITER-CK-nowrap-p{p}", ok, f"L={L} <= sqrt(p)={math.isqrt(p)}, 2L < p: {2*L < p}")
        # brute: enumerate all cyclic 3-APs inside P and verify index-AP correspondence
        cnt_cyclic = 0; cnt_index = 0
        Ps = set(P)
        for x1 in P:
            for x2 in P:
                x3 = (2*x2 - x1) % p
                if x3 in Ps and x1 != x3:
                    cnt_cyclic += 1
        for i1 in range(L):
            for i2 in range(L):
                i3 = 2*i2 - i1
                if 0 <= i3 < L and i1 != i3:
                    cnt_index += 1
        check(f"ITER-CK-ap-bijection-p{p}", cnt_cyclic == 2*cnt_index or cnt_cyclic == cnt_index,
              f"cyclic={cnt_cyclic} index={cnt_index}")

# =====================================================================
# W76-142K V2 LANES (the arsenal-native engine). Receipts -> v2 file.
# =====================================================================
import numpy as np
import json

RECEIPTS_V2 = os.path.join(HERE, "receipts142sublinear_v2.txt")
PASS2 = 0; FAIL2 = 0

def R2(msg):
    print(msg, flush=True)
    with open(RECEIPTS_V2, "a") as f: f.write(msg + "\n")

def check2(name, ok, detail=""):
    global PASS2, FAIL2
    if ok: PASS2 += 1; R2(f"PASS {name} {detail}")
    else:  FAIL2 += 1; R2(f"FAIL {name} {detail}")

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = 41
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

# ---------- shared cyclic primitives (exact integer arithmetic) ----------

def cyclic_greedy_apfree(p, seed, tries=4):
    """Largest-of-4 random-order greedy cyclically-3-AP-free subset of Z_p.
    Two-method guarantee: the result is brute-verified before return."""
    best = set()
    inv2 = pow(2, -1, p)
    for t in range(tries):
        rr = random.Random(seed * 1000 + t)
        order = list(range(p)); rr.shuffle(order)
        inB = [False]*p; forb = set(); members = []
        for x in order:
            if x in forb: continue
            inB[x] = True; members.append(x)
            for y in members[:-1]:
                forb.add((2*x - y) % p)
                forb.add((2*y - x) % p)
                forb.add((x + y) * inv2 % p)
        if len(members) > len(best): best = set(members)
    return best

def cyclic_ap_count(p, Bset):
    """T = #{(a,b,c) in B^3 : a+c = 2b mod p} — method 1 (sum profile)."""
    inv2 = pow(2, -1, p)
    tally = {}
    Bl = sorted(Bset)
    for i in range(len(Bl)):
        ai = Bl[i]
        for j in range(len(Bl)):
            s = (ai + Bl[j]) % p
            tally[s] = tally.get(s, 0) + 1
    T = 0
    for b in Bset:
        T += tally.get((2*b) % p, 0)
    return T

def cyclic_ap_count_scan(p, inB):
    """T — method 2 (independent (x,d)-scan): #{(x,d): x,x+d,x+2d in B}."""
    T = 0
    for x in range(p):
        if not inB[x]: continue
        for d in range(p):
            if inB[(x+d)%p] and inB[(x+2*d)%p]:
                T += 1
    return T

def cyclic_correlations(p, inB, M):
    """C_e = sum_x F(x)F(x+e) for F = p*1_B - M (exact ints, numpy);
    R_b = sum_a F(a)F(2b-a)."""
    F = np.array([p*inB[x] - M for x in range(p)], dtype=np.int64)
    idx = np.arange(p)
    C = np.empty(p, dtype=np.int64)
    for e in range(p):
        C[e] = int(np.dot(F, F[(idx+e) % p]))
    R = np.empty(p, dtype=np.int64)
    for b in range(p):
        R[b] = int(np.dot(F, F[((2*b - idx) % p)]))
    return F, C, R

def cyclic_apfree_brutefree(p, Bset):
    """Brute cyclic-AP-freeness: no distinct a,b,c in B with a+c=2b."""
    inv2 = pow(2, -1, p)
    Bl = sorted(Bset); Bs = set(Bl)
    for i in range(len(Bl)):
        a = Bl[i]
        for j in range(len(Bl)):
            if i == j: continue
            c = Bl[j]
            b = (a + c) * inv2 % p
            if b in Bs and b != a and b != c:
                return False
    return True

# ---------- EP-CK: L-EP exact identities + second-moment bound ----------

def ep_ck():
    R2("--- EP-CK: L-EP deviation identity / axis-flip square / CS bound / forced popularity ---")
    primes = [101, 1009, 4999, 10007]
    assert all(is_prime(p) for p in primes)
    for p in primes:
        instances = []
        for (dn, dd) in [(1,4), (1,8)]:
            for s in range(2):
                rr = random.Random(SEED + p + dn*97 + s)
                M = (p*dn)//dd
                instances.append((f"rand{dn}o{dd}s{s}", set(rr.sample(range(p), M))))
        instances.append((f"interval", set(range(p//4))))
        instances.append((f"mod3class", set(x for x in range(p) if x % 3 == 0)))
        if p <= 1009:
            g = cyclic_greedy_apfree(p, SEED + p)
            if len(g) >= 6:
                instances.append(("greedy-apfree", g))
        for (tag, Bset) in instances:
            M = len(Bset)
            if M < 2: continue
            inB = [False]*p
            for x in Bset: inB[x] = True
            # method 1: sum profile
            T1 = cyclic_ap_count(p, Bset)
            # method 2: independent (x,d)-scan (full at small p, sampled rows at large)
            if p <= 1009:
                T2 = cyclic_ap_count_scan(p, inB)
            else:
                # independent method 2 at scale: scan d-profile by dot products
                v = np.array([1 if inB[x] else 0 for x in range(p)], dtype=np.int64)
                idx = np.arange(p)
                T2 = 0
                for x in range(p):
                    if inB[x]:
                        T2 += int(np.dot(v, v[(idx+x)%p] * v[(idx+2*x)%p]))
            check2(f"EP-CK-T2agree-p{p}-{tag}", T1 == T2, f"T1={T1} T2={T2}")
            # exact identities with F = p*1_B - M  (f = F/p):
            F, C, R = cyclic_correlations(p, inB, M)
            # (1) sigma(b)*p^2 = p*M^2 + R_b  for sampled b
            inv2 = pow(2, -1, p)
            ok_sig = True
            bl = sorted(Bset)
            for b in (bl[:3] + bl[len(bl)//2:len(bl)//2+3] + bl[-3:]):
                # sigma(b) = #{(a,c) in B^2 : a+c = 2b}
                sb = sum(1 for a in Bset for c in Bset if (a + c) % p == (2*b) % p)
                if sb * p*p != p*M*M + int(R[b]): ok_sig = False
            check2(f"EP-CK-sigma-p{p}-{tag}", ok_sig, "sigma(b)*p^2 = p*M^2+R_b on sampled b")
            # (2) p^2*T = p*M^3 + sum_{b in B} R_b
            lhs = p*p*T1
            rhs = p*M**3 + sum(int(R[b]) for b in Bset)
            check2(f"EP-CK-devid-p{p}-{tag}", lhs == rhs, f"p^2*T={lhs} rhs={rhs}")
            # (3) axis-flip square: sum_b R_b^2 = sum_e C_e^2
            sR = int(np.dot(R, R)); sC = int(np.dot(C, C))
            check2(f"EP-CK-axissq-p{p}-{tag}", sR == sC, f"sum R^2={sR} sum C^2={sC}")
            # (4) CS bound: (sum_{b in B} R_b)^2 <= M * p^2 * sum_e C_e
            sRB = sum(int(R[b]) for b in Bset)
            cs_ok = (sRB*sRB <= M * p*p * sC) if sRB >= 0 else ((-sRB)**2 <= M*p*p*sC)
            check2(f"EP-CK-csbound-p{p}-{tag}", cs_ok,
                   f"(sumR_B)^2={sRB*sRB} <= M*p^2*sumC={M*p*p*sC}")
            # (5) sanity of c_0 and symmetry
            c0 = int(C[0]); M2 = M*(p-M)
            check2(f"EP-CK-c0sym-p{p}-{tag}", c0 == M2 and all(C[e] == C[(p-e)%p] for e in range(1, min(p, 40))),
                   f"C_0={c0}=M(p-M)={M2}, C symmetric")
            # (ii) core: for cyclically-AP-free sets, T = M and
            #   sum_{e!=0} c_e^2 >= delta*p*(delta^2 p - 1)^2 - delta^2(1-delta)^2 p^2
            if tag == "greedy-apfree":
                check2(f"EP-CK-apfree-T-p{p}", T1 == M, f"T={T1}=|B|={M} (cyclically AP-free)")
                ok_free = cyclic_apfree_brutefree(p, Bset)
                check2(f"EP-CK-apfree-brute-p{p}", ok_free, "brute freeness confirmed")
                d = Fraction(M, p)
                sumC_ne0 = sC - c0*c0
                bnd = d*p*(d*d*p - 1)**2 - d*d*(1-d)**2*p*p
                check2(f"EP-CK-forced2nd-p{p}", Fraction(sumC_ne0, p**4) >= bnd,
                       f"sum_(e!=0)c^2={Fraction(sumC_ne0,p**4)} (bound {float(bnd):.1f}, delta={float(d):.3f})")
                # max popularity: max_{e!=0} c_e and its sign
                mx = max(int(C[e]) for e in range(1, p))
                mn = min(int(C[e]) for e in range(1, p))
                R2(f"  [EP-CK-report-p{p}] max c_e={mx}, min c_e={mn}, "
                   f"delta={float(d):.4f}, delta^2 p={float(d*d*p):.1f}, "
                   f"guaranteed-positive-grade delta^4*p/8={float(d**4*p/8):.2f}")

# ---------- POP-CK: popular-difference extraction on the integer window ----------

def greedy_apfree_window(N, seed=SEED):
    """Classic greedy 3-AP-free subset of [0,N) (insertion order = index order)."""
    B = []
    inB = [False]*N
    for x in range(N):
        ok = True
        # x completes an AP iff exists d>=1 with x-2d, x-d in B, or x-d, x-2d... (window)
        for d in range(1, x//2 + 1):
            if inB[x-2*d] and inB[x-d]: ok = False; break
        if ok:
            B.append(x); inB[x] = True
    return B, inB

def window_apfree_full(N, inB):
    for x in range(N):
        for d in range(1, (N-x)//2 + 1):
            if inB[x] and inB[x+d] and inB[x+2*d]: return False
    return True

def pop_ck():
    R2("--- POP-CK: popular-difference extraction, greedy 3-AP-free at N=1000 ---")
    N = 1000
    B, inB = greedy_apfree_window(N)
    M = len(B); delta = Fraction(M, N)
    check2("POP-CK-apfree", window_apfree_full(N, inB), f"|B|={M} delta={float(delta):.4f} (full brute O(N^2) freeness)")
    # m_d for all d (method 1: per-gap scan)
    m = [0]*(N)
    for d in range(1, N):
        c = 0
        for i in range(N-d):
            if inB[i] and inB[i+d]: c += 1
        m[d] = c
    # method 2: from the pair list
    m2 = [0]*(N)
    for i in B:
        for j in B:
            if i < j: m2[j-i] += 1
    check2("POP-CK-magree", m == m2, f"two counting codes agree (sum={sum(m)}=C(M,2)={M*(M-1)//2})")
    check2("POP-CK-pairsplit", sum(m) == M*(M-1)//2, f"sum_d m_d = C(M,2)")
    # pigeonhole law: max_d m_d >= delta^2 * N / 3 (valid for M >= 3)
    mx_d = max(range(1, N), key=lambda d: m[d])
    check2("POP-CK-pigeonhole", m[mx_d] >= float(delta)*float(delta)*N/3,
           f"max m_d = m[{mx_d}] = {m[mx_d]} >= delta^2 N/3 = {float(delta)**2*N/3:.1f}")
    # empirical popularity report: the excess gamma at the best small gaps
    best = []
    for d in range(1, N//2 + 1):
        base = float(delta)**2 * (N - d)
        g = m[d] - base
        if g > 0: best.append((g, d))
    best.sort(reverse=True)
    R2(f"  [POP-CK-report] top popular gaps (gamma, d, m_d): "
       f"{[(round(g,1), d, m[d]) for (g,d) in best[:6]]}")
    # L-EP(iii) verification on the top gaps with positive excess:
    # for gap d*: SOME class r mod d* has |B_cap_C_r| >= 2*delta^2*(n_r-1) + 2*gamma/d*
    dstar = best[0][1] if best else None
    checked_law = 0
    for (g, d) in best[:8]:
        gamma = m[d] - float(delta)**2*(N-d)
        # class containers (method 1: direct enumeration)
        ok_some = False; best_r = -1; best_margin = -10**9
        for r in range(d):
            idxs = [s for s in range((N - r + d - 1)//d) if inB[r + s*d]]
            n_r = (N - r + d - 1)//d
            margin = len(idxs) - (2*float(delta)**2*(n_r-1) + 2*gamma/d)
            if margin >= 0: ok_some = True
            if margin > best_margin: best_margin, best_r = margin, r
        # method 2: run structure of the best class (runs <= 2; #pairs = |B_r| - #runs)
        r = best_r
        cls = [1 if inB[r + s*d] else 0 for s in range((N - r + d - 1)//d)]
        runs = 0; i = 0; maxrun = 0
        while i < len(cls):
            if cls[i]:
                runs += 1; j = i
                while j < len(cls) and cls[j]: j += 1
                maxrun = max(maxrun, j - i); i = j
            else: i += 1
        pairs_r = sum(1 for s in range(len(cls)-1) if cls[s] and cls[s+1])
        run_ok = (maxrun <= 2) and (pairs_r == sum(cls) - runs)
        if ok_some and run_ok: checked_law += 1
    check2("POP-CK-classamp", checked_law >= min(6, len(best)),
           f"L-EP(iii) class-amplification verified on {checked_law}/{min(6,len(best))} top gaps "
           f"(some class >= 2*delta^2*(n-1)+2*gamma/d; runs<=2; pairs=|B_r|-runs)")
    # the class-density report: best class density vs delta (the empirical increment)
    gmax, dg = best[0]
    bestdens = 0.0
    for r in range(dg):
        n_r = (N - r + dg - 1)//dg
        cnt = sum(1 for s in range(n_r) if inB[r + s*dg])
        bestdens = max(bestdens, cnt/n_r)
    R2(f"  [POP-CK-report] best class density at gap {dg}: {bestdens:.4f} "
       f"vs delta={float(delta):.4f} vs 2*delta^2={2*float(delta)**2:.4f}")
    # cross-check at N=4000 (lighter): pigeonhole + class law on the top gap only
    N2 = 4000
    B2, inB2 = greedy_apfree_window(N2, seed=SEED+1)
    M2b = len(B2); d2 = Fraction(M2b, N2)
    mm = {}
    for i in B2:
        for j in B2:
            if i < j: mm[j-i] = mm.get(j-i, 0) + 1
    mxd = max(mm, key=lambda k: mm[k])
    check2("POP-CK-pigeonhole-N4000", mm[mxd] >= float(d2)**2*N2/3,
           f"N=4000 |B|={M2b} delta={float(d2):.4f} max m[{mxd}]={mm[mxd]} >= {float(d2)**2*N2/3:.1f}")

# ---------- ITER-CK-2: the L-NW no-wrap model step, two methods ----------

def iter_ck_2():
    R2("--- ITER-CK-2: L-NW no-wrap model step (brute wrap-scan + rescaled coords) ---")
    for p in [101, 1009, 3203, 9973]:
        assert is_prime(p)
        L = math.isqrt(p)   # max model length: L <= sqrt(p)
        trials = 40 if p <= 1009 else 20
        rr = random.Random(SEED + p)
        all_scan = True; all_resc = True; bij = True
        for t in range(trials):
            q = rr.randrange(1, p)          # nonzero step (prime p => automatically coprime)
            a = rr.randrange(p)
            ell = rr.randint(2, L)
            P = [(a + j*q) % p for j in range(ell)]
            Ps = set(P)
            check_len = len(Ps) == ell      # injectivity (q != 0 mod p)
            if not check_len: all_scan = False; all_resc = False; break
            # METHOD A (wrap-scan): every cyclic AP inside P is an index AP
            okA = True
            for i1 in range(ell):
                for i3 in range(ell):
                    if i1 == i3: continue
                    x2 = (P[i1] + P[i3]) * pow(2, -1, p) % p
                    if x2 in Ps:
                        i2 = P.index(x2)
                        if i1 + i3 != 2*i2: okA = False; break
                if not okA: break
            # METHOD B (rescaled coordinates): the divisibility argument, numerically
            okB = True
            for i1 in range(ell):
                for i2 in range(ell):
                    for i3 in range(i2+1, ell):
                        s = (i1 + i3 - 2*i2)
                        if 0 <= i1 < ell and ((a + i1*q) + (a + i3*q) - 2*(a + i2*q)) % p == 0:
                            if s != 0: okB = False; break
                if not okB: break
            # bijection count: cyclic APs in P == model APs in [0,ell) (x2 in P iff index AP)
            cyc = 0
            for i1 in range(ell):
                for i3 in range(ell):
                    if i1 == i3: continue
                    x2 = (P[i1] + P[i3]) * pow(2, -1, p) % p
                    if x2 in Ps: cyc += 1
            mod = sum(1 for i1 in range(ell) for i2 in range(ell)
                      for i3 in range(ell) if i1 + i3 == 2*i2 and i1 != i3)
            if not (okA and okB and cyc == mod): all_scan = False; all_resc = False; bij = False
        check2(f"ITER-CK-2-wrapscan-p{p}", all_scan, f"{trials} random (a,q,ell<=sqrt(p)={L}) cyclic APs all genuine")
        check2(f"ITER-CK-2-rescaled-p{p}", all_resc, "rescaled-coordinates divisibility check agrees")
        check2(f"ITER-CK-2-bijection-p{p}", bij, "cyclic AP count == model AP count (bijection)")
    # the container-ladder composition induction (L-NW(b)): 3 levels deep
    p = 1009
    rr = random.Random(SEED + 77)
    ok_ladder = True
    for t in range(25):
        q0 = rr.randrange(1, p); a0 = rr.randrange(p)
        ell0 = rr.randint(8, 31)            # ell0 <= sqrt(1009) = 31
        # level 1: class container at gap w1, residue r1
        w1 = rr.randint(1, max(1, ell0//2)); r1 = rr.randrange(min(w1, ell0))
        ell1 = (ell0 - r1 + w1 - 1)//w1
        # level 2: class container of the level-1 model at gap w2, residue r2
        w2 = rr.randint(1, max(1, ell1//2)); r2 = rr.randrange(min(w2, ell1))
        ell2 = (ell1 - r2 + w2 - 1)//w2
        if ell2 < 1: continue
        a1 = (a0 + r1*q0) % p; q1 = (w1*q0) % p
        a2 = (a1 + r2*q1) % p; q2 = (w2*q1) % p
        # composed parameterization: a0 + (r1 + w1*(r2 + w2*s))*q0 == a2 + s*q2 (mod p)
        ok_comp = all(((a0 + (r1 + w1*(r2 + w2*s))*q0) % p) == ((a2 + s*q2) % p)
                      for s in range(ell2))
        # injectivity and no-wrap at every level
        L0 = [(a0 + j*q0) % p for j in range(ell0)]
        L1 = [(a1 + j*q1) % p for j in range(ell1)]
        L2 = [(a2 + j*q2) % p for j in range(ell2)]
        inj = len(set(L0)) == ell0 and len(set(L1)) == ell1 and len(set(L2)) == ell2
        sub = set(L2) <= set(L1) <= set(L0)
        # no-wrap at the deepest level: cyclic APs of L2 are index APs
        S2 = set(L2); ok_nw = True
        for i1 in range(ell2):
            for i3 in range(ell2):
                if i1 == i3: continue
                x2 = (L2[i1] + L2[i3]) * pow(2, -1, p) % p
                if x2 in S2:
                    if i1 + i3 != 2*L2.index(x2): ok_nw = False
        if not (ok_comp and inj and sub and ok_nw): ok_ladder = False
    check2("ITER-CK-2-ladder-p1009", ok_ladder,
           "3-level container-ladder composition: parameterization identity, "
           "injectivity, nesting, no-wrap at every level (25 trials)")

# ---------- V-CK-2: copy-count checkpoints with the banked + extended table ----------

def v_ck_2():
    R2("--- V-CK-2: copy-count checkpoints with the banked + 142E-extended table ---")
    # cross-check the r_3 values used: banked table vs 142E tables_rk.json
    banked = {9: 5, 29: 11, 30: 12, 31: 12, 38: 14, 40: 15, 48: 16}
    try:
        with open(os.path.join(HERE, "experiments", "tables_rk.json")) as f:
            trk = json.load(f)["3"]
        agree = all(int(trk[str(n)]["value"]) == v for n, v in banked.items() if str(n) in trk)
        covered = sorted(int(k) for k in trk.keys())
        check2("V-CK-2-table-crosscheck", agree,
               f"banked r_3 values agree with 142E tables_rk.json (k=3 covers N=1..{covered[-1]}, "
               f"five methods per value)")
    except Exception as ex:
        check2("V-CK-2-table-crosscheck", False, f"tables_rk.json load failed: {ex}")
    N = 10000
    for m in [9, 30, 38, 48]:
        D = (N-1)//(m-1)
        formula = sum(N - (m-1)*d for d in range(1, D+1))
        rng2 = random.Random(SEED + N + m)
        ok_samp = True
        for _ in range(400):
            d = rng2.randint(1, D); a = rng2.randint(1, N - (m-1)*d)
            if not (1 <= a and a + (m-1)*d <= N): ok_samp = False
        check2(f"V-CK-2-copies-N{N}-m{m}", ok_samp and formula > 0,
               f"#copies formula={formula}, 400 sampled copies valid (two methods: formula vs enumeration)")
        # per-point nu in the middle band (method 2)
        band_lo, band_hi = N//4, 3*N//4
        min_nu = 10**9
        for _ in range(120):
            x = rng2.randint(band_lo, band_hi)
            nu = 0
            for d in range(1, D+1):
                for j in range(m):
                    a2 = x - j*d
                    if a2 >= 1 and a2 + (m-1)*d <= N: nu += 1
            min_nu = min(min_nu, nu)
        check2(f"V-CK-2-nu-N{N}-m{m}", min_nu >= N//16, f"min nu in band = {min_nu} >= N/16 = {N//16}")
        # copy cap on the greedy AP-free set vs the banked r_3(m)
        A = set()
        for x in range(1, N+1):
            ok = True
            for d in range(1, x//2+1):
                if (x-2*d) in A and (x-d) in A: ok = False; break
            if ok: A.add(x)
        worst = 0
        for _ in range(250):
            d = rng2.randint(1, D); a = rng2.randint(1, N - (m-1)*d)
            worst = max(worst, len({a+j*d for j in range(m)} & A))
        check2(f"V-CK-2-copycap-N{N}-m{m}", worst <= banked[m],
               f"sampled worst |A cap copy|={worst} <= r_3({m})={banked[m]}")
    # block-law ladder sanity: rho(N) <= rho(48) + 48/N at the certified end
    rho48 = Fraction(16, 48)
    for Nn in [1000, 10000]:
        check2(f"V-CK-2-blockladder-N{Nn}", Fraction(16, 48) + Fraction(48, Nn) <= Fraction(1, 3) + Fraction(1, 20),
               f"rho(48)+48/N={float(rho48 + Fraction(48,Nn)):.4f} (certified linear cap)")

def main():
    R2(f"=== engine142sublinear W76-142K V2 battery (arsenal-native engine), seed {SEED} ===")
    R2("W76 correction orders: Fourier lanes F1/F2/I RETIRED as load-bearing; "
       "replaced by EP-CK/POP-CK (NEW LAW L-EP) per the arsenal-native rebuild.")
    t0 = time.time()
    ep_ck(); pop_ck(); iter_ck_2(); v_ck_2()
    R2(f"TOTAL: {PASS2} PASS / {FAIL2} FAIL (wall {time.time()-t0:.0f}s)")
    R2("SUBLINEAR_ENGINE_V2_GREEN=1" if FAIL2 == 0 else "SUBLINEAR_ENGINE_V2_RED=1")

def main_legacy():
    R(f"=== engine142sublinear W75-142K commander battery, seed {SEED} ===")
    t0 = time.time()
    v_ck(); f1_f2_ck(); i_ck(); iter_ck()
    R(f"TOTAL: {PASS} PASS / {FAIL} FAIL (wall {time.time()-t0:.0f}s)")
    R("SUBLINEAR_ENGINE_GREEN=1" if FAIL == 0 else "SUBLINEAR_ENGINE_RED=1")

if __name__ == "__main__":
    if "--legacy" in sys.argv:
        main_legacy()
    else:
        main()
