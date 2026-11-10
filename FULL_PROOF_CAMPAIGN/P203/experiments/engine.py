#!/usr/bin/env python3
"""P203 covering-tree engine.

Problem: cover Z^2 by ONE coset of Lambda_q per prime q, where
Lambda_q = {(k,l): 2^k 3^l = 1 mod q} (index h_q = |<2,3>_q|). Then CRT gives m.

Tree calculus (all verified by coset arithmetic):
  Region R = off + L (L a rank-2 sublattice of Z^2, index D).
  Prime q acts via phi_q(k,l) = U*k + V*l mod h_q (surjective, ker = Lambda_q).
  phi_q(L) = <g1,g2> <= Z/h_q, m_q = h_q / gcd(h_q,g1,g2).
   - m_q = 1  => Lambda_R <= Lambda_q: q ABSORBS R by W_q := phi_q(off).
   - m_q >= 2 => q SPLITS R: cylinder^R = ONE coset of L^Lambda_q (the child
     containing off, when W_q := phi_q(off)); the other m_q-1 cosets stay open.
  Tree closes (no open regions) => covering of Z^2 => CRT => m witness.
"""
import json, math, random, sys, time
from math import gcd

def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)

def hnf(rows):
    """Row-style HNF of lattice spanned by rows (2x2). Returns (a,b),(0,d), a,d>0, 0<=b<d."""
    (a1, b1), (a2, b2) = rows
    # column 1: gcd of a1,a2 with combo
    g, x, y = egcd(a1, a2) if (a1 or a2) else (0, 0, 0)
    if g < 0: g, x, y = -g, -x, -y
    r1 = (a1 * x + a2 * y, b1 * x + b2 * y)   # first coord = g
    r2 = (0, (a2 * b1 - a1 * b2) // (g if g else 1))  # first coord 0 (det/g)
    if g == 0:
        # degenerate: both first coords 0
        d = gcd(abs(b1), abs(b2))
        if d == 0: return ((1, 0), (0, 1))
        return ((1, 0), (0, d))
    if r1[1] < 0: r1 = (-r1[0], -r1[1]) if r1[0] > 0 else r1
    if r1[0] < 0: r1 = (-r1[0], -r1[1]); r2 = (-r2[0], -r2[1])
    a, b = r1[0] % r1[0] if r1[0] else 0, r1[1] % (r2[1] if r2[1] else 1)
    # reduce r1 by r2 in second coord
    if r2[1] != 0:
        t = r1[1] // r2[1]
        r1 = (r1[0], r1[1] - t * r2[1])
        if r1[1] < 0 and r2[1] > 0:
            r1 = (r1[0], r1[1] + r2[1])
    return (r1, r2)

def lat_index(r1, r2):
    return abs(r1[0] * r2[1] - r1[1] * r2[0])

def canon(r1, r2, off):
    """canonical form of region off + <r1,r2>."""
    (r1, r2) = hnf((r1, r2))
    a, b = r1; d = r2[1]
    # reduce off: k mod a, then l
    k0, l0 = off
    t = 0
    if a > 0:
        t = k0 // a
        k0 = k0 - t * a
    l0 = l0 - t * b
    if d > 0:
        s = l0 // d
        l0 = l0 - s * d
    if k0 < 0:  # safety
        k0 += a; l0 += b
    if l0 < 0: l0 += d
    return (r1, r2, k0, l0)

class Prime:
    __slots__ = ("p", "h", "U", "V", "o2", "o3")
    def __init__(self, rec):
        self.p = rec["p"]; self.h = rec["h"]
        self.U = rec.get("U"); self.V = rec.get("V")
        self.o2 = rec["o2"]; self.o3 = rec["o3"]

def phi(pr, k, l):
    return (pr.U * k + pr.V * l) % pr.h

def region_action(pr, r1, r2):
    """m = |phi(L)| ; returns (m, g1, g2) or None if no U,V."""
    if pr.U is None: return None
    h = pr.h
    g1 = (pr.U * r1[0] + pr.V * r1[1]) % h
    g2 = (pr.U * r2[0] + pr.V * r2[1]) % h
    m = h // gcd(h, gcd(g1, g2))
    return (m, g1, g2)

def modpow_test(pr, r1, r2):
    """q | 2^a 3^b - 1 for both generators (handles negatives)."""
    p = pr.p
    for (a, b) in (r1, r2):
        v = pow(2, a, p) * pow(3, b, p) % p   # negative exps OK in py3.8+ w/ inverse
        if v != 1: return False
    return True

def split_region(pr, reg):
    """Split region by prime q. Returns (children, W) where children = list of
    canonical open regions (m-1 of them). Sets nothing; caller records W_q."""
    r1, r2, k0, l0 = reg
    h = pr.h
    m, g1, g2 = region_action(pr, r1, r2)
    assert m >= 2
    G = gcd(g1, g2)
    x, y = g1 // G, g2 // G
    # find (alpha,beta): x*alpha + y*beta = 1
    g, alpha, beta = egcd(x, y)
    assert abs(g) == 1
    if g < 0: alpha, beta = -alpha, -beta
    # kernel basis in t-space: (y,-x), m*(alpha,beta)
    # children reps: j*(alpha,beta)*B
    B = (r1, r2)
    children = []
    for j in range(1, m):
        v = (j * alpha % m, j * beta % m)  # reduce j*(alpha,beta) mod K via m*(alpha,beta)
        c1 = (v[0] * r1[0] + v[1] * r2[0], v[0] * r1[1] + v[1] * r2[1])
        # child lattice = K*B = <(y,-x)*B, m(alpha,beta)*B>
        w1 = (y * r1[0] - x * r2[0], y * r1[1] - x * r2[1])
        w2 = (m * alpha * r1[0] + m * beta * r2[0], m * alpha * r1[1] + m * beta * r2[1])
        children.append(canon(w1, w2, (k0 + c1[0], l0 + c1[1])))
    W = phi(pr, k0, l0)
    return children, W

def absorb_W(pr, reg):
    """If m==1, the W that makes q cover the whole region."""
    r1, r2, k0, l0 = reg
    return phi(pr, k0, l0)

def target_modpow(pr, reg):
    """2^k0 3^l0 mod p (the cylinder constant for modpow-tested primes)."""
    k0, l0 = reg[2], reg[3]
    return pow(2, k0, pr.p) * pow(3, l0, pr.p) % pr.p

# ---------------- search ----------------

class Search:
    def __init__(self, palette, heur):
        self.palette = [Prime(r) for r in palette if r.get("U") is not None]
        self.palette_big = [Prime(r) for r in palette if r.get("U") is None]
        self.heur = heur
        # identity region: Z^2 = <(1,0),(0,1)>, offset (0,0)
        self.root = ((1, 0), (0, 1), 0, 0)

    def run(self, seed=0, verbose=True, max_regions=600, node_cap=20000):
        rng = random.Random(seed)
        regions = [self.root]
        used = {}          # prime index -> W (int) or ('modpow', target)
        used_set = set()
        t0 = time.time()
        nodes = 0
        while regions:
            nodes += 1
            if nodes > node_cap: return None
            # ---- absorption pass (cheapest, most valuable) ----
            absorbed = True
            while absorbed and regions:
                absorbed = False
                # try to absorb each region (smallest D first: likely deepest)
                for i in sorted(range(len(regions)), key=lambda j: lat_index(*regions[j][:2])):
                    reg = regions[i]
                    r1, r2, k0, l0 = reg
                    # (a) used primes with matching W (FREE)
                    free = False
                    for qi, (pr, W) in used.items():
                        act = region_action(pr, r1, r2)
                        if act and act[0] == 1 and phi(pr, k0, l0) == W:
                            free = True; break
                        if pr.U is None:
                            continue
                    if free:
                        regions.pop(i); absorbed = True; break
                    # (b) unused palette primes, prefer smallest h (budget)
                    best = None
                    for pi, pr in enumerate(self.palette):
                        if pi in used_set: continue
                        act = region_action(pr, r1, r2)
                        if act and act[0] == 1:
                            if best is None or pr.h < self.palette[best].h:
                                best = pi
                    if best is not None:
                        pr = self.palette[best]
                        used[best] = (pr, phi(pr, k0, l0))
                        used_set.add(best)
                        regions.pop(i); absorbed = True; break
                    # (c) big/modpow primes
                    for pi, pr in enumerate(self.palette_big):
                        if pi in used_big: continue
                        if modpow_test(pr, r1, r2):
                            used_big[pi] = (pr, target_modpow(pr, reg))
                            regions.pop(i); absorbed = True; break
                    if absorbed: break
                # end for
            # end while absorbed
            if not regions: break
            if len(regions) > max_regions: return None
            # ---- split pass ----
            # pick region by heuristic
            if self.heur["region"] == "maxD":
                ri = max(range(len(regions)), key=lambda j: lat_index(*regions[j][:2]))
            elif self.heur["region"] == "minD":
                ri = min(range(len(regions)), key=lambda j: lat_index(*regions[j][:2]))
            else:
                ri = rng.randrange(len(regions))
            reg = regions[ri]
            r1, r2 = reg[0], reg[1]
            # candidate splitters: unused palette primes with m>=2
            cands = []
            for pi, pr in enumerate(self.palette):
                if pi in used_set: continue
                act = region_action(pr, r1, r2)
                if act and act[2] != 1 or (act and act[0] >= 2):
                    if act[0] >= 2:
                        cands.append((pi, act[0]))
            if not cands: return None
            # scorer
            def score(pi, m):
                pr = self.palette[pi]
                if self.heur["split"] == "minm":   return (-m, 1.0 / pr.h)
                if self.heur["split"] == "maxh":   return (1.0 / pr.h, -m)
                if self.heur["split"] == "minmh":  return (m / pr.h, -m)  # balance
                return (rng.random(),)
            rng.shuffle(cands)
            cands.sort(key=lambda c: score(*c))
            pi, m = cands[0]
            pr = self.palette[pi]
            children, W = split_region(pr, reg)
            used[pi] = (pr, W)
            used_set.add(pi)
            regions.pop(ri)
            # dedup children
            seen = set()
            for ch in children:
                key = (ch[0], ch[1], ch[2], ch[3])
                if key not in seen:
                    seen.add(key); regions.append(ch)
            if verbose and nodes % 20 == 0:
                bud = sum(1.0 / pr.h for pr, _ in used.values())
                print(f"  nodes={nodes} regions={len(regions)} used={len(used)} "
                      f"budget={bud:.3f} t={time.time()-t0:.0f}s", flush=True)
        # success
        return used, used_big

def main():
    palette = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "palette.json"))
    global used_big
    heur = {"region": sys.argv[2] if len(sys.argv) > 2 else "maxD",
            "split": sys.argv[3] if len(sys.argv) > 3 else "minm"}
    for seed in range(int(sys.argv[4]) if len(sys.argv) > 4 else 1):
        used_big = {}
        S = Search(palette, heur)
        res = S.run(seed=seed)
        if res:
            used, ub = res
            print(f"SUCCESS seed={seed} heur={heur}")
            bud = sum(1.0 / pr.h for pr, _ in used.values()) + \
                  sum(1.0 / pr.h for pr, _ in ub.values())
            print(f"primes used: {len(used)+len(ub)}, budget {bud:.4f}")
            json.dump({"heur": heur, "seed": seed,
                       "assign": [{"p": pr.p, "h": pr.h, "U": pr.U, "V": pr.V, "W": W}
                                  for pr, W in used.values()] +
                                  [{"p": pr.p, "h": pr.h, "target": W}
                                   for pr, W in ub.values()]},
                      open(f"cover_{heur['region']}_{heur['split']}_{seed}.json", "w"))
            return
        else:
            print(f"seed {seed}: no cover", flush=True)

used_big = {}
main()
