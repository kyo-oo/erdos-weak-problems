#!/usr/bin/env python3
"""#1212 ROUND 4 — THE MODULUS-LADDER BLOCK SEARCH (translation-resonance, general M).

THE UNIFORM SCHEDULING LEMMA (round-4, the generalization of round-3's band
{2..10} to the modulus ladder). Fix a modulus M = 2 * prod(QCOV) (QCOV = odd
coverage primes) and a vertex v = (x, y) with
  (BAND)  1 <= x - y <= DMAX   (every prime <= DMAX divides M),
  (B)     for every q in QCOV:  q | (x - y) -> q does not divide x,
  (PAR)   not (2 | x and 2 | y),
  (COV)   some q in {2} u QCOV divides x or y.
Then for EVERY t >= 0 the translated vertex (x + M*t, y + M*t) is a #1212
G-vertex: min > 1, gcd = 1, at least one composite coordinate.
Proof: any prime p of gcd(x+Mt, y+Mt) divides x - y <= DMAX, hence p | M;
p = 2 dies by (PAR) (2 | M); p in QCOV gives p | x and p | y (p | M), so
p | (x-y) and p | x — dead by (B). Compositeness: the carrier q of (COV)
divides x + Mt for all t (q | M), q >= 2, q*q <= 121 < x <= x + Mt.

THE BLOCK: a monotone hub-walk of M moves (M/2 x-moves + M/2 y-moves of +2
each, via the mixed intermediates), net translation (M, M), whose every
vertex satisfies BAND+(B)+(COV) [hubs: BAND d in 2..DMAX even; intermediates:
d +- 1 odd]. Concatenating period copies gives the INFINITE PATH — the FULL
YES for #1212.

LANES (the live d-graph analysis: hub-d even with odd prime factors in QCOV;
x-move d -> d+2 needs d+1 odd-smooth; y-move d -> d-2 needs d-1 odd-smooth):
  210  = 2*3*5*7   : tube {2,4,6,8,10} (5 diagonals) — round-3 lane, FAILED.
  2310 = 2*3*5*7*11: tube {2,4,6,8,10,12} (6 diagonals) — the round-4 candidate.
  2730 = 2*3*5*7*13: tubes {2..10} (5, with 13-carrier) and {12,14,16} (3).
The DP: states (t, j) with d = d0 + 2j; X = X0 + t + j; Y = Y0 + t - j.
Output: block data + dual verification.

Usage: engine1212_round4.py [lane] [chunk_seconds] — checkpoint-resumable.
"""
import sys, json, time, os

def odd_primes_of(n):
    qs = []
    for q in (3, 5, 7, 11, 13):
        if n % q == 0:
            qs.append(q)
    return tuple(qs)

class Lane:
    def __init__(self, M):
        self.M = M
        self.QCOV = odd_primes_of(M)
        # valid hub-d: even, >= 2, odd prime factors all in QCOV (cap 60)
        self.DHUB = [d for d in range(2, 61) if d % 2 == 0 and
                     all(p in self.QCOV for p in odd_pf(d))]
        # valid intermediate-d': odd, prime factors all in QCOV (cap 61)
        self.DINT = [e for e in range(1, 62) if e % 2 == 1 and
                     all(p in self.QCOV for p in odd_pf(e))]
        self.DHUBs = set(self.DHUB)
        self.DINTs = set(self.DINT)
        self.half = M // 2

def odd_pf(n):
    out = []
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59):
        if n % p == 0:
            out.append(p)
    return out

def make_checkers(lane, X0, Y0):
    Q = lane.QCOV
    def hub_ok(X, Y):
        d = X - Y
        if d not in lane.DHUBs:
            return False
        for q in Q:
            if d % q == 0 and X % q == 0:
                return False  # (B)
        for q in Q:
            if X % q == 0 or Y % q == 0:
                return True   # (COV)
        return False
    def xedge_ok(X, Y):
        d1 = (X - Y) + 1
        if d1 not in lane.DINTs:
            return False
        for q in Q:
            if d1 % q == 0 and (X + 1) % q == 0:
                return False
        return True
    def yedge_ok(X, Y):
        d1 = (X - Y) - 1
        if d1 not in lane.DINTs:
            return False
        for q in Q:
            if d1 % q == 0 and X % q == 0:
                return False
        return True
    return hub_ok, xedge_ok, yedge_ok

def search_base(lane, X0, Y0, d0, JMAX=40):
    """Forward DP over (t, j). Returns vertex list or (None, max_t)."""
    M = lane.M
    hub_ok, xedge_ok, yedge_ok = make_checkers(lane, X0, Y0)
    # state (t, j) reachable; parent[(t,j)] = (pj, move)
    if not hub_ok(X0, Y0):
        return None, 0
    frontier = {0}
    parent = {}
    maxt = 0
    for t in range(0, M):
        if not frontier:
            break
        nxt = set()
        for j in frontier:
            X = X0 + t + j
            Y = Y0 + t - j
            # x-move: (t,j) -> (t+1, j+1); intermediate (X+1, Y); hub (X+2, Y)
            if abs(j + 1) <= JMAX and xedge_ok(X, Y):
                X2, Y2 = X + 2, Y
                if hub_ok(X2, Y2):
                    s = (t + 1, j + 1)
                    if s not in parent:
                        parent[s] = (j, 'x')
                        nxt.add(j + 1)
            # y-move
            if abs(j - 1) <= JMAX and yedge_ok(X, Y):
                X2, Y2 = X, Y + 2
                if hub_ok(X2, Y2):
                    s = (t + 1, j - 1)
                    if s not in parent:
                        parent[s] = (j, 'y')
                        nxt.add(j - 1)
        frontier = nxt
        if frontier:
            maxt = t + 1
    if (M, 0) not in parent:
        return None, maxt
    # reconstruct moves backward from (t=M, j=0)
    moves = []
    t, j = M, 0
    while (t, j) != (0, 0):
        if (t, j) not in parent:
            return None, maxt
        pj, mv = parent[(t, j)]
        moves.append(mv)
        t, j = t - 1, pj
    moves.reverse()
    assert len(moves) == M
    assert moves.count('x') == lane.half and moves.count('y') == lane.half
    # emit vertices: hub0, then per move: intermediate + hub
    verts = [(X0, Y0)]
    x, y = X0, Y0
    for mv in moves:
        if mv == 'x':
            verts.append((x + 1, y))
            x += 2
        else:
            verts.append((x, y + 1))
            y += 2
        verts.append((x, y))
    assert verts[-1] == (X0 + M, Y0 + M)
    return verts, M

def base_X0(lane, u):
    """smallest odd X0 >= half with X0 = u (mod half) — hmm: residue mod M/2
    determines all conditions (period of the pattern is lcm(QCOV))."""
    h = lane.half
    X0 = u + h if u % 2 == 0 else u + 2 * h
    return X0

def run_lane(lane_name, M, time_budget, ckpt_file, d0_list=None, verbose=True):
    lane = Lane(M)
    if d0_list is None:
        d0_list = [d for d in lane.DHUB if d <= 12]
    ck = {"next_i": 0, "found": None}
    if os.path.exists(ckpt_file):
        with open(ckpt_file) as f:
            ck = json.load(f)
        if ck["found"]:
            return ck["found"], lane
    bases = []
    for d0 in d0_list:
        for u in range(lane.half):
            bases.append((d0, u))
    t0 = time.time()
    i = ck["next_i"]
    stats = {"tried": 0, "maxt_best": 0}
    while i < len(bases):
        if time.time() - t0 > time_budget:
            ck["next_i"] = i
            with open(ckpt_file, "w") as f:
                json.dump(ck, f)
            if verbose:
                print(f"[{lane_name}] CHUNK BUDGET hit at base {i}/{len(bases)} "
                      f"(tried {stats['tried']}, best depth {stats['maxt_best']})")
            return None, lane
        d0, u = bases[i]
        X0 = base_X0(lane, u)
        Y0 = X0 - d0
        if Y0 >= 2:
            verts, maxt = search_base(lane, X0, Y0, d0)
            stats["tried"] += 1
            if maxt > stats["maxt_best"]:
                stats["maxt_best"] = maxt
            if verts is not None:
                res = {"d0": d0, "u": u, "X0": X0, "Y0": Y0, "M": M,
                       "verts": verts}
                ck["found"] = res
                with open(ckpt_file, "w") as f:
                    json.dump(ck, f)
                return res, lane
        i += 1
    ck["next_i"] = i
    with open(ckpt_file, "w") as f:
        json.dump(ck, f)
    if verbose:
        print(f"[{lane_name}] EXHAUSTED: no block. bases={len(bases)}, "
              f"best depth {stats['maxt_best']}/{M}")
    return None, lane

def diagnostic_210():
    """Independent re-verification of the round-3 NO verdict (lane 210)."""
    lane = Lane(210)
    depths = []
    n_start_bad = 0
    for d0 in (6, 4, 8, 2, 10):
        for u in range(105):
            X0 = base_X0(lane, u)
            Y0 = X0 - d0
            verts, maxt = search_base(lane, X0, Y0, d0)
            depths.append(maxt)
            if maxt == 0:
                n_start_bad += 1
    import collections
    hist = collections.Counter(depths)
    print("LANE 210 DIAGNOSTIC: 525 bases, ALL FAIL (independent DP re-verification)")
    print("  start-hub-invalid bases:", n_start_bad)
    print("  death-depth histogram (t reached):", dict(sorted(hist.items())))
    print("  max depth reached over all bases:", max(depths), "/ 210")
    return None

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "diag210"
    if cmd == "diag210":
        diagnostic_210()
    elif cmd in ("2310", "2730", "210"):
        budget = float(sys.argv[2]) if len(sys.argv) > 2 else 480.0
        M = int(cmd)
        ck = f"ckpt1212_lane{M}.json"
        res, lane = run_lane(cmd, M, budget, ck)
        if res:
            print(f"FOUND BLOCK: M={M} d0={res['d0']} u={res['u']} "
                  f"base=({res['X0']},{res['Y0']}) vertices={len(res['verts'])}")
            with open(f"block1212_lane{M}.json", "w") as f:
                json.dump(res, f)
        else:
            print("no block yet (or exhausted)")
    else:
        print("usage: engine1212_round4.py [diag210|210|2310|2730] [budget_s]")
