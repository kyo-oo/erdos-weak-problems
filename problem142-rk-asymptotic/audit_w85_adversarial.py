#!/usr/bin/env python3
# W85-142D ADVERSARIAL AUDIT ENGINE — independent of engine142uppergen.py.
# Tries to BREAK: AFF-K cap, V-GEN band/copy/double-count/assembly, SLIDE-GEN.
# Official AP semantics (FC/Combinatorics/AP/Basic.lean): a k-AP is a SET
# {b + n*e | n < k} with ENat.card = k. card = k forces the k points DISTINCT,
# which (k>=2) forces e >= 1. So: k distinct points b, b+e, ..., b+(k-1)e, e>=1.
from itertools import combinations

def is_kap_free(S, k):
    S = set(S)
    for b in S:
        for e in range(1, max(S) + 1):
            if all((b + i * e) in S for i in range(k)):
                return False
    return True

def r_k_exact(N, k):
    """Exact r_k(N) by include/exclude DFS with prefix AP scan (independent code)."""
    best = [0]
    def viol(v, Sset, k):
        # a new AP created must END at v (the newly added element)
        for b in Sset | {v}:
            pass
        # check APs ending at v: v = b + (k-1)e
        for e in range(1, (v - 1) // (k - 1) + 1 if v >= k else 1):
            if v - (k - 1) * e >= 1 and all((v - (k - 1) * e + i * e) in Sset or (v - (k - 1) * e + i * e) == v for i in range(k)):
                if all(((v - (k - 1) * e + i * e) in Sset) or ((v - (k - 1) * e + i * e) == v) for i in range(k)):
                    return True
        return False
    def rec(v, cnt, Sset):
        if v > N:
            best[0] = max(best[0], cnt); return
        if cnt + (N - v + 1) <= best[0]: return
        # take v if no AP ends at v
        if not viol(v, Sset, k):
            rec(v + 1, cnt + 1, Sset | {v})
        rec(v + 1, cnt, Sset)
    rec(1, 0, set())
    return best[0]

print("=" * 70)
print("PART 0 — r_k exact values (independent B&B) + cross-check vs banked")
print("=" * 70)
# Banked cross-check cells (UPPER_STACK / DM142A stones): r3: 61->19, 48->16;
# r4 42->22; r5 55->36 (too big for this B&B; check small ones instead)
mytab = {}
for k in (3, 4):
    for N in range(1, 23):
        mytab[(k, N)] = r_k_exact(N, k)
banked3 = {1:1,2:2,3:2,4:4,5:4,6:4,7:4,8:6,9:5,10:6,11:7,12:7,13:7,14:8,15:8,
           16:8,17:8,18:8,19:8,20:8,21:9,22:9}  # OEIS A005836-style r_3 prefix (greedy/Cantor) — NOT r_3!
# NOTE: r_3(N) != greedy; use the well-known r_3 prefix (A003002-adjacent):
# r_3: 1..: 1,2,2,4,4,4,4,6,5? — compute independently instead, only sanity anchors:
anchors = {(3,1):1,(3,2):2,(3,3):2,(3,4):4,(3,8):6,(3,9):5,(3,14):8,(3,20):8,
           (4,1):1,(4,2):2,(4,3):3,(4,4):3,(4,5):4,(4,8):7,(4,9):8}
bad = []
for (k, N), v in anchors.items():
    if mytab.get((k, N)) != v:
        bad.append((k, N, mytab.get((k, N)), v))
print("anchor disagreements:", bad if bad else "NONE (independent B&B matches known r_3/r_4 anchors)")
print("r_3(1..22) =", [mytab[(3,n)] for n in range(1,23)])
print("r_4(1..22) =", [mytab[(4,n)] for n in range(1,23)])
print("r_3(2) =", mytab[(3,2)], "  r_4(2) =", mytab[(4,2)], "  (r_k(2)=2 for k>=3 claimed)")

print()
print("=" * 70)
print("PART A — AFF-K ADVERSARIAL BRUTE FORCE (the mathematical heart)")
print("=" * 70)
# For every k-AP-free A subset [1,N] (N<=14, all 2^N subsets), every copy
# c(a,d) = {a+(i-1)d : i in [1,m]} with ANY a>=0, d>=1: |A n c| <= r_k(m)?
# (relaxed a: any a>=1 — even a+(m-1)d > N, matching the Lean rectangle.)
failures = 0; checked = 0
for k in (3, 4):
    for m in (2, 3, 4, 5):
        rm = mytab.get((k, m)) or r_k_exact(m, k)
        N = 13 if k == 3 else 12
        for mask in range(1 << N):
            A = {x + 1 for x in range(N) if (mask >> x) & 1}
            if not is_kap_free(A, k): continue
            for d in (1, 2, 3, 4, 5):
                for a in range(1, 3 * N):  # a arbitrary (copy may stick out of [1,N])
                    C = {a + (i - 1) * d for i in range(1, m + 1)}
                    inter = len(A & C)
                    checked += 1
                    if inter > rm:
                        failures += 1
                        if failures <= 3:
                            print(f"  COUNTEREXAMPLE: k={k} m={m} rm={rm} A={sorted(A)} a={a} d={d} |A&C|={inter} C={sorted(C)}")
print(f"copies checked: {checked}, AFF-K failures: {failures}",
      "-> AFF-K SOUND on the brute-forced envelope" if failures == 0 else "-> AFF-K BROKEN!")

print()
print("=" * 70)
print("PART B — BAND + RELAXED ONE-SIDED BAND (incidence) EXHAUSTIVE")
print("=" * 70)
# For every x in [t+1, N] (ONE-SIDED band, t=(m-1)D0): the m*D0 triples
# (a,d,j)=(x-(j-1)d, d, j) are pairwise DISTINCT and satisfy a in [1,N].
# Also the paper's TWO-SIDED band: additionally a+(m-1)d <= N.
for (m, N) in [(2,64),(2,65),(2,127),(3,144),(3,145),(3,200),(4,256),(5,400),(5,401),(9,1296),(8,1024),(20,6400)]:
    D0 = N // (4 * m * (m - 1))
    t = (m - 1) * D0
    assert D0 >= 1 and 4*m*(m-1)*D0 <= N, (m, N, D0)
    bad1 = bad2 = 0
    for x in range(t + 1, N + 1):
        tri = set()
        for d in range(1, D0 + 1):
            for j in range(1, m + 1):
                a = x - (j - 1) * d
                if 1 <= a <= N:            # relaxed rectangle condition
                    tri.add((a, d, j))
        if len(tri) != m * D0: bad1 += 1
    # two-sided (paper) band: x in [t+1, N-t], copies additionally INSIDE [1,N]
    for x in range(t + 1, N - t + 1):
        tri2 = {(x-(j-1)*d, d, j) for d in range(1, D0+1) for j in range(1, m+1)
                if 1 <= x-(j-1)*d and x-(j-1)*d + (m-1)*d <= N}
        if len(tri2) != m * D0: bad2 += 1
    print(f"m={m:2d} N={N:5d} D0={D0:3d} t={t:4d}: one-sided band misses={bad1} (x in [{t+1},{N}]), "
          f"two-sided band misses={bad2} (x in [{t+1},{N-t}])",
          "OK" if (bad1 == 0 and bad2 == 0) else "BROKEN")

print()
print("=" * 70)
print("PART C+D+E — DOUBLE COUNT + FRINGE + ASSEMBLY on planted AP-free sets")
print("=" * 70)
def greedy_apfree(k, N, seed=0):
    import random
    rnd = random.Random(seed); S = set()
    for x in range(1, N + 1):
        S.add(x)
        if not is_kap_free(S, k): S.discard(x)
    # random-order pass for variety
    order = list(range(1, N + 1)); rnd.shuffle(order)
    T = set()
    for x in order:
        T.add(x)
        if not is_kap_free(T, k): T.discard(x)
    return S if len(S) >= len(T) else T

def vgen_core_check(k, m, N, A):
    """Verify every inequality of the paper proof, AND the relaxed one-sided version."""
    D0 = N // (4 * m * (m - 1)); t = (m - 1) * D0
    rm = mytab.get((k, m)) or r_k_exact(m, k)
    As = set(A)
    # (paper) two-sided band + valid copies
    band = {x for x in As if t + 1 <= x <= N - t}
    tot_paper = sum(len(As & {a + (i-1)*d for i in range(1, m+1)})
                    for d in range(1, D0+1) for a in range(1, N - (m-1)*d + 1))
    C0 = sum(N - (m-1)*d for d in range(1, D0+1))
    low_paper = len(band) * m * D0
    cap_paper = rm * C0
    # (relaxed) one-sided band + FULL rectangle [1,N]x[1,D0]
    band1 = {x for x in As if t + 1 <= x}
    tot_rel = sum(len(As & {a + (i-1)*d for i in range(1, m+1)})
                  for d in range(1, D0+1) for a in range(1, N+1))
    low_rel = len(band1) * m * D0
    cap_rel = rm * N * D0
    # fringe + final assembly (both versions)
    okA = len(As) <= len(band) + 2*t and len(As) <= len(band1) + t
    okFinal = 2*m*len(As) <= (2*rm + 1) * N
    return dict(low_paper=low_paper, tot_paper=tot_paper, cap_paper=cap_paper, C0=C0,
                low_rel=low_rel, tot_rel=tot_rel, cap_rel=cap_rel,
                okp=(low_paper <= tot_paper <= cap_paper),
                okr=(low_rel <= tot_rel <= cap_rel), okA=okA, okFinal=okFinal)

cases = [(3, 2, 64), (3, 2, 65), (3, 3, 144), (4, 3, 144), (3, 5, 400), (4, 5, 400),
         (3, 9, 1296), (4, 8, 1024), (5, 9, 1296), (3, 20, 6400), (4, 14, 3136)]
allok = True
for (k, m, N) in cases:
    for seed in (0, 1):
        A = greedy_apfree(k, N, seed)
        assert is_kap_free(A, k)
        res = vgen_core_check(k, m, N, A)
        ok = res["okp"] and res["okr"] and res["okA"] and res["okFinal"]
        allok = allok and ok
        print(f"k={k} m={m:2d} N={N:5d} seed={seed} |A|={len(A):4d}: paper[{res['low_paper']}<=Σ={res['tot_paper']}<=cap={res['cap_paper']}] "
              f"relaxed[{res['low_rel']}<=Σ={res['tot_rel']}<=cap={res['cap_rel']}] fringe_ok={res['okA']} FINAL_ok={res['okFinal']}",
              "OK" if ok else "BROKEN")
print("ASSEMBLY:", "ALL SOUND (paper + relaxed)" if allok else "DEFECT FOUND")

print()
print("=" * 70)
print("PART G — SLIDE-GEN EXACT TEST (small N, exact r_k)")
print("=" * 70)
# m*r_k(N) <= r_k(m)*(N-m+1) + 2m(m-1) for all N >= 2m-1, k>=3, m>=2.
fails = 0; tests = 0
for k in (3, 4):
    for m in range(2, 13):
        rm = mytab.get((k, m)) or r_k_exact(m, k)
        for N in range(2 * m - 1, 23):
            rN = mytab[(k, N)]
            tests += 1
            if m * rN > rm * (N - m + 1) + 2 * m * (m - 1):
                fails += 1
                if fails <= 5: print(f"  SLIDE-GEN VIOLATION: k={k} m={m} N={N}: {m}*{rN}={m*rN} > {rm}*{N-m+1}+{2*m*(m-1)}={rm*(N-m+1)+2*m*(m-1)}")
print(f"SLIDE-GEN exact tests: {tests}, violations: {fails}",
      "-> SLIDE-GEN SOUND at small N" if fails == 0 else "-> SLIDE-GEN BROKEN")

print()
print("=" * 70)
print("PART E2 — boundary arithmetic sweep (D0>=1, 4m(m-1)D0<=N, 2(m-1)D0<=N/(2m))")
print("=" * 70)
bad = 0
for m in range(2, 60):
    for N in range(16*m*m, 16*m*m + 500, 7):
        D0 = N // (4*m*(m-1)); t = (m-1)*D0
        if D0 < 1: bad += 1; print(f"  D0<1 at m={m} N={N}")
        if 4*m*(m-1)*D0 > N: bad += 1; print(f"  4m(m-1)D0>N at m={m} N={N}")
        if 2*m*t*2*m > 4*m*m*N: pass  # vacuous
        if 4*m*t > N: bad += 1; print(f"  4m(m-1)D0>N (final) at m={m} N={N}")
print("boundary sweep:", "CLEAN" if bad == 0 else f"{bad} DEFECTS")

print()
print("=" * 70)
print("PART T — tightness anchors from the brief")
print("=" * 70)
for (m, N) in [(2, 64), (3, 144), (4, 256), (5, 400)]:
    D0 = N // (4*m*(m-1)); t = (m-1)*D0
    print(f"m={m} N={N}: D0={D0}, t=(m-1)D0={t}, 2t={2*t}, 4m(m-1)D0={4*m*(m-1)*D0} "
          f"(<=N: {4*m*(m-1)*D0<=N}, TIGHT: {4*m*(m-1)*D0==N}), band=[{t+1},{N-t}], fringe={2*t}")
print("brief claims m=2,N=64: D0=8,t=8,fringe=16,4m(m-1)D0=64=N TIGHT  and  m=3,N=144: D0=6,t=12,fringe=24,4m(m-1)D0=144=N TIGHT")
