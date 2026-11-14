#!/usr/bin/env python3
# check939_w66.py — THE INDEPENDENT RE-DERIVATION AUDIT of the table939_w66
# package (W66-P939-E). Deliberately shares NO code with engine939_w66.py:
# fresh sieve, fresh recursive-DFS generation (the prior-hunt code path,
# corrected: exponents 4,5,6,...), fresh brute double-loop sum census,
# fresh lane census. Every emitted file is re-validated byte-semantically.
#
# Usage: python3 check939_w66.py [--fast]
#   --fast : skip the 1e14 structure-free brute census (keeps DFS + lanes).
# Writes CHECK939_W66_RESULT.txt. Exit code 0 iff everything passes.
import sys, os, math, json, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
RES = []

def P(name, ok, detail=''):
    line = f'{"PASS" if ok else "FAIL"} {name}' + (f' — {detail}' if detail else '')
    print(line, flush=True)
    RES.append(line)
    return ok

# ---------- fresh sieve ----------
def sieve(limit):
    if limit < 2: return []
    b = bytearray([1]) * (limit + 1); b[0:2] = b'\x00\x00'
    i = 2
    while i * i <= limit:
        if b[i]: b[i*i::i] = b'\x00' * len(range(i*i, limit + 1, i))
        i += 1
    return [j for j in range(2, limit + 1) if b[j]]

def iroot(n, k):
    if n < 2: return 0
    x = int(round(n ** (1.0 / k)))
    while x > 0 and x ** k > n: x -= 1
    while (x + 1) ** k <= n: x += 1
    return x

# ---------- fresh generation: recursive DFS (independent path) ----------
def gen4_dfs(limit):
    P4 = sieve(iroot(limit, 4))
    out = []
    def rec(i, val):
        out.append(val)
        for j in range(i, len(P4)):
            v = val * P4[j] ** 4
            if v > limit: break
            while v <= limit:
                rec(j + 1, v)
                v *= P4[j]
    rec(0, 1)
    out = [x for x in out if 1 <= x <= limit]
    out.sort()
    return out

# ---------- fresh brute predicate ----------
def rpowerful(n, r=4):
    if n < 1: return False
    if n == 1: return True
    m = n; d = 2
    while d * d <= m:
        if m % d == 0:
            cnt = 0
            while m % d == 0: m //= d; cnt += 1
            if cnt < r: return False
        d += 1 if d == 2 else 2
    return m == 1 or m == 0

def brute_census(limit):
    return [n for n in range(1, limit + 1) if rpowerful(n)]

# ---------- fresh brute double-loop sum census ----------
def brute_pairs(L, B):
    Ls = set(L); hits = []
    n = len(L)
    for i in range(n):
        a = L[i]; rem = B - a
        for j in range(i, n):
            b = L[j]
            if b > rem: break
            if (a + b) in Ls: hits.append((a, b, a + b))
    return hits

# ---------- fresh lane census ----------
def lane_pairs(L, B, do_ee=True):
    O = [x for x in L if x & 1]; E = [x for x in L if not (x & 1)]
    Es = set(E)
    hits = []
    for r in (1, 3, 5, 7, 9, 11, 13, 15):
        bk = [o for o in O if (o & 15) == r]
        for ii in range(len(bk)):
            for c in bk[ii + 1:]:
                if (c - bk[ii]) in Es:
                    e = c - bk[ii]
                    hits.append((min(e, bk[ii]), max(e, bk[ii]), c, 'EO'))
    for r in (1, 3, 5, 7):
        ba = [o for o in O if (o & 15) == r]
        bb = [o for o in O if (o & 15) == (16 - r)]
        for a in ba:
            for b in bb:
                if a + b > B: break
                if (a + b) in Es:
                    hits.append((min(a, b), max(a, b), a + b, 'OO'))
    if do_ee:
        nE = len(E)
        for i in range(nE):
            a = E[i]; rem = B - a
            for j in range(i, nE):
                b = E[j]
                if b > rem: break
                if (a + b) in Es: hits.append((a, b, a + b, 'EE'))
    return hits

def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for blk in iter(lambda: fh.read(1 << 20), b''): h.update(blk)
    return h.hexdigest()

def read_values(tag):
    with open(os.path.join(HERE, f'values939_{tag}.txt')) as fh:
        return [int(x) for x in fh.read().split()]

def read_hits(tag):
    rows = []
    with open(os.path.join(HERE, f'sumhits939_{tag}.tsv')) as fh:
        for ln in fh:
            if ln.startswith('#') or not ln.strip(): continue
            a, b, c, g, lane, pc = ln.rstrip('\n').split('\t')
            rows.append((int(a), int(b), int(c), int(g), lane, pc))
    return rows

def check_bound(tag, brute_sum=False, do_ee=True):
    dig = int(tag[2:])
    B = 10 ** dig
    t0 = time.time()
    Lf = read_values(tag)
    Ld = gen4_dfs(B)
    P(f'{tag} values file == fresh DFS regeneration', Ld == Lf,
      f'{len(Lf)} values; DFS {time.time() - t0:.1f}s')
    if dig <= 6:
        P(f'{tag} values == brute predicate scan', Ld == brute_census(B))
    # delta + lean chunk files
    with open(os.path.join(HERE, f'values939_{tag}.delta.txt')) as fh:
        dl = []
        for ln in fh:
            ln = ln.strip()
            if not ln or ln.startswith('#'): continue
            dl.append(int(ln))
    v = dl[0]; rec = [v]
    for d in dl[1:]: v += d; rec.append(v)
    P(f'{tag} delta file reconstructs the value list', rec == Lf)
    chunks = []
    with open(os.path.join(HERE, f'values939_{tag}.lean.txt')) as fh:
        for ln in fh:
            ln = ln.strip()
            if ln.startswith('--') or not ln: continue
            chunks.append([int(x) for x in ln.strip('[]').split(',')])
    P(f'{tag} lean chunk file reconstructs the value list (25/chunk)',
      [x for ch in chunks for x in ch] == Lf and all(len(ch) == 25 for ch in chunks))
    # sum-hit table
    rows = read_hits(tag)
    Ls = set(Lf)
    ok_rows = True; bad = None
    seen = set()
    for (a, b, c, g, lane, pc) in rows:
        lane_ok = ((lane == 'EE' and a % 2 == 0 and b % 2 == 0) or
                   (lane == 'EO' and (a % 2) != (b % 2)) or
                   (lane == 'OO' and a % 2 == 1 and b % 2 == 1))
        if not (a <= b and a + b == c and c <= B and a in Ls and b in Ls
                and c in Ls and g == math.gcd(a, b) and lane_ok
                and pc == ('YES' if g == 1 else 'no')):
            ok_rows = False; bad = (a, b, c, g, lane, pc); break
        key = (a, b, c, lane)
        if key in seen: ok_rows = False; bad = ('dup', key); break
        seen.add(key)
    P(f'{tag} sumhits rows self-consistent (a+b=c, membership, gcd, lane, '
      f'no dupes)', ok_rows, f'{len(rows)} rows; bad={bad}')
    hits_fresh = lane_pairs(Ld, B, do_ee=do_ee)
    hits_fresh_set = {(a, b, c, lane) for (a, b, c, lane) in hits_fresh}
    P(f'{tag} sumhits table == fresh lane re-derivation',
      hits_fresh_set == seen, f'file {len(seen)} vs fresh {len(hits_fresh_set)}')
    if brute_sum:
        t0 = time.time()
        bp = brute_pairs(Ld, B)
        bset = {(a, b, c) for (a, b, c) in bp}
        fset = {(a, b, c) for (a, b, c, _) in hits_fresh}
        P(f'{tag} fresh lane census == structure-free brute double loop',
          bset == fset, f'{len(bset)} vs {len(fset)}; brute {time.time() - t0:.1f}s')
    # coverage json
    cov = json.load(open(os.path.join(HERE, f'coverage939_{tag}.json')))
    P(f'{tag} coverage counts', cov['count_incl_1'] == len(Lf) and
      cov['count_excl_1'] == len(Lf) - 1 and cov['min_value'] == Lf[0]
      and cov['max_value'] == Lf[-1])
    P(f'{tag} coverage parity/buckets',
      cov['parity']['odd'] == sum(1 for v in Lf if v & 1) and
      cov['parity']['even'] == sum(1 for v in Lf if not (v & 1)) and
      all(cov['mod16_odd_buckets'][str(r)] ==
          sum(1 for v in Lf if v & 1 and (v & 15) == r)
          for r in (1, 3, 5, 7, 9, 11, 13, 15)))
    dec = cov['per_decade_counts']
    from bisect import bisect_right
    okd = all(dec[f'1e{k}'] == bisect_right(Lf, 10 ** (k + 1) - 1) -
              bisect_right(Lf, 10 ** k - 1) for k in range(dig))
    P(f'{tag} coverage per-decade counts', okd)
    gaps = [Lf[i + 1] - Lf[i] for i in range(len(Lf) - 1)]
    mg = min(gaps); mi = gaps.index(mg)
    P(f'{tag} coverage min gap', cov['min_gap'] == mg and
      cov['min_gap_pair'] == [Lf[mi], Lf[mi + 1]])
    runs = cov['sorted_disjoint_ranges']
    okr = sum(r[2] for r in runs) == len(Lf) and all(
        r[0] <= r[1] and r[2] == sum(1 for v in Lf if r[0] <= v <= r[1])
        for r in runs) and all(runs[i][1] < runs[i + 1][0]
        for i in range(len(runs) - 1))
    P(f'{tag} coverage sorted disjoint ranges (sum/rows/order)', okr,
      f'{len(runs)} range rows')
    gvals = {}
    for (a, b, c, g, lane, pc) in rows: gvals[g] = gvals.get(g, 0) + 1
    P(f'{tag} coverage gcd histogram + min_hit_gcd',
      cov['gcd_histogram'] == {str(k): v for k, v in sorted(gvals.items())}
      and cov['min_hit_gcd'] == (min(gvals) if gvals else None))
    P(f'{tag} coverage sum-hit totals by lane',
      cov['sum_hits_total'] == len(rows) and
      all(cov['sum_hits_by_lane'][ln] ==
          sum(1 for r in rows if r[4] == ln) for ln in ('EE', 'EO', 'OO')))
    nzc = not any(r[5] == 'YES' for r in rows)
    P(f'{tag} THE BOX CLAIM: zero coprime rows => zero pairwise-coprime '
      f'triples <= {tag}', cov['zero_coprime_witnesses'] is True and nzc)
    for fn, want in cov['sha256'].items():
        P(f'{tag} sha256 {fn}', sha256(os.path.join(HERE, fn)) == want)
    return nzc

def main():
    fast = '--fast' in sys.argv
    t0 = time.time()
    P('P0 fresh DFS gen reproduces the K60 Lean census row at 1e4',
      gen4_dfs(10 ** 4) == [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729,
      1024, 1296, 2048, 2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561,
      7776, 8192, 10000])
    allz = True
    allz &= check_bound('1e13', brute_sum=True, do_ee=True)
    allz &= check_bound('1e14', brute_sum=not fast, do_ee=True)
    allz &= check_bound('1e15', brute_sum=False, do_ee=True)
    # box19 if present
    b19 = os.path.join(HERE, 'values939_1e19.txt')
    if os.path.exists(b19):
        t0 = time.time()
        Lf = [int(x) for x in open(b19).read().split()]
        Ld = gen4_dfs(10 ** 19)
        P('1e19 values file == fresh DFS regeneration', Ld == Lf,
          f'{len(Lf)} values; DFS {time.time() - t0:.1f}s')
        rows = read_hits('1e19')
        Ls = set(Ld)
        okr = all(a + b == c and a in Ls and b in Ls and c in Ls and
                  g == math.gcd(a, b) and lane in ('EO', 'OO') and pc == 'no'
                  for (a, b, c, g, lane, pc) in rows)
        P('1e19 sumhits rows self-consistent (EO/OO only, all gcd>1)', okr,
          f'{len(rows)} rows')
        hits_fresh = lane_pairs(Ld, 10 ** 19, do_ee=False)
        fset = {(a, b, c, lane) for (a, b, c, lane) in hits_fresh}
        sset = {(a, b, c, r[4]) for r in rows}
        P('1e19 sumhits == fresh lane re-derivation', fset == sset,
          f'{len(fset)} vs {len(sset)}')
        cov = json.load(open(os.path.join(HERE, 'coverage939_1e19.json')))
        P('1e19 box claim: zero coprime rows',
          cov['zero_coprime_witnesses'] is True and
          not any(r[5] == 'YES' for r in rows) and
          cov['count_incl_1'] == len(Lf))
        allz &= True
    verdict = all(r.startswith('PASS') for r in RES)
    RES.append('')
    RES.append(f'CHECK939_W66 {"ALL_OK" if verdict else "HAS_FAILURES"} '
               f'({time.time() - t0:.1f}s, fast={fast})')
    with open(os.path.join(HERE, 'CHECK939_W66_RESULT.txt'), 'w') as fh:
        fh.write('\n'.join(RES) + '\n')
    print(RES[-1])
    sys.exit(0 if verdict else 1)

if __name__ == '__main__':
    main()
