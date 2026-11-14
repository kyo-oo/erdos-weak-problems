#!/usr/bin/env python3
# engine939_w66.py — W66-P939-E: INDEPENDENT SECOND-METHOD CENSUS + TABLE EMISSION
# Erdős #939 (r-powerful sums), r=4 lane. Task W66-P939-E.
#
# ALGORITHMIC INDEPENDENCE from the existing hunts (hunt939b/c/d/e):
#   * GENERATION — Method A ("layered per-prime sorted-merge DP"): primes are
#     processed in ASCENDING order; the running list L holds all 4-powerful
#     values composed of primes already processed; for each prime p, every
#     v in L with v <= limit//p^4 is extended by p^e (e = 4,5,6,...) and the
#     additions are merged into L (two sorted runs -> Timsort C-speed merge).
#     Each 4-powerful n is produced EXACTLY ONCE (at the layer of its largest
#     prime factor; unique decomposition n = v * p^e with v p-free of primes
#     >= p) — no dedup needed. The prior hunts use depth-first recursion over
#     exponent vectors with an append-then-sort pass: a different code path.
#   * PREDICATE — the Lean kernel fold (Erdos939R4.lean: rpow r n = 1 <= n &
#     divAll r n n) is simulated LITERALLY (divAll over every e in [1,n]) and
#     proved equivalent on all n <= 3000 to the fast trial-division predicate;
#     the fast predicate is then cross-checked against sympy.factorint on all
#     n <= 10^6, and the DP generator is cross-checked against a brute
#     predicate scan at 10^4/10^5/10^6 and against the K60 Lean census row.
#   * SUM CENSUS — Method S1 (transparent double loop over the sorted list
#     with set membership; no structure assumed) and Method S2 (the mod-16
#     lane decomposition EE/EO/OO, implemented with plain dict buckets and
#     per-lane pure-python scans). At the primary box (1e13) BOTH run and
#     must agree exactly; S2 (math-forced complete lane decomposition) runs
#     at the extended bounds.
#
# The box theorem being evidenced: every pair (a,b) of 4-powerful numbers with
# a+b 4-powerful (a+b <= B) has gcd(a,b) > 1 — equivalently (see the
# gcd-equality lemma, verified numerically on every hit): there is NO
# pairwise-coprime 4-powerful triple a+b=c with c <= B.
#
# Edge handling (cross-checked against the Lean def): n = 1 is vacuously
# 4-powerful (empty factorization; divAll's e=1 row passes since prime 1 =
# false); rpow4(0) = false; the triple 1+1=2 fails since 2 is not 4-powerful.
# The value lists EMITTED HERE INCLUDE 1 (matching the Lean predicate); all
# reported counts also give the exclude-1 figure for comparison with the
# prior-hunt convention (their gen4 dropped 1).
#
# Usage: engine939_w66.py <phase> [arg]
#   phases: validate | census <13|14|15|16> | counts | box19 | help
# Long phases write checkpoints into table939_w66/ so progress survives.
import sys, os, time, math, json, hashlib
from bisect import bisect_right, bisect_left

REPO = os.path.dirname(os.path.abspath(__file__))
TAB = os.path.join(REPO, 'table939_w66')
T0 = time.time()

LEAN_CENSUS_R4 = [1, 16, 32, 64, 81, 128, 243, 256, 512, 625, 729, 1024, 1296,
                  2048, 2187, 2401, 2592, 3125, 3888, 4096, 5184, 6561, 7776,
                  8192, 10000]

_logf = None
def log(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    if _logf is not None:
        _logf.write(s + '\n'); _logf.flush()

def open_log(tag):
    global _logf
    os.makedirs(TAB, exist_ok=True)
    _logf = open(os.path.join(TAB, 'engine939_w66_output.txt'), 'a')
    log(f'=== engine939_w66 phase {tag} start; python {sys.version.split()[0]}; '
        f'{time.strftime("%Y-%m-%d %H:%M:%S")} ===')

# ---------------------------------------------------------------------------
# integer k-th root (float-free; small guards for float error)
# ---------------------------------------------------------------------------
def iroot(n, k):
    if n < 0: raise ValueError
    if n < 2: return 0
    x = int(round(n ** (1.0 / k)))
    while x > 0 and x ** k > n: x -= 1
    while (x + 1) ** k <= n: x += 1
    return x

# ---------------------------------------------------------------------------
# own prime sieve (bytearray Eratosthenes) — independent of sympy
# ---------------------------------------------------------------------------
def sieve(limit):
    if limit < 2: return []
    b = bytearray([1]) * (limit + 1)
    b[0:2] = b'\x00\x00'
    for i in range(2, iroot(limit, 2) + 1):
        if b[i]:
            b[i*i::i] = b'\x00' * len(range(i*i, limit + 1, i))
    return [i for i in range(2, limit + 1) if b[i]]

_PR_CACHE = {}
def primes_to(n):
    if n not in _PR_CACHE:
        _PR_CACHE.clear()
        _PR_CACHE[n] = sieve(n)
    return _PR_CACHE[n]

# ---------------------------------------------------------------------------
# PREDICATES
# ---------------------------------------------------------------------------
def lean_prime(n):
    """Mirrors Erdos939R4.lean `prime n = Nat.ble 2 n && noDivFrom (n-1) n`:
    n >= 2 and no e in [2, n-1] divides n."""
    if n < 2: return False
    for e in range(2, n):
        if n % e == 0: return False
    return True

def lean_rpow(r, n, lp=None):
    """LITERAL simulation of Erdos939R4.lean:
    rpow r n = decide (1 <= n && divAll r n n = true) where divAll folds
    e = 1..n with (n % e != 0 || !(prime e) || n % e^r == 0).
    lp: optional precomputed lean_prime table for speed."""
    if n < 1: return False
    for e in range(1, n + 1):
        if n % e == 0:
            isp = lp[e] if lp is not None else lean_prime(e)
            if isp and n % (e ** r) != 0:
                return False
    return True

def rpowerful(n, r):
    """Fast r-powerful predicate (airtight full trial division to sqrt)."""
    if n < 1: return False
    if n == 1: return True
    m = n; d = 2
    while d * d <= m:
        if m % d == 0:
            cnt = 0
            while m % d == 0:
                m //= d; cnt += 1
            if cnt < r: return False
        d += 1 if d == 2 else 2
    if m > 1: return False      # leftover prime has exponent 1 < r (r >= 2)
    return True

# ---------------------------------------------------------------------------
# GENERATION — Method A: layered per-prime sorted-merge DP (the second path)
# ---------------------------------------------------------------------------
def gen4_dp(limit, include_one=True):
    r4 = iroot(limit, 4)
    P = primes_to(r4)
    L = [1]
    for p in P:
        p4 = p * p * p * p
        if p4 > limit:
            break
        cutoff = limit // p4
        i = bisect_right(L, cutoff)
        if i == 0:
            continue
        adds = []
        ap = adds.append
        for v in L[:i]:
            q = v * p4
            while q <= limit:
                ap(q)
                q *= p
        if adds:
            adds.sort()
            L = sorted(L + adds)   # two sorted runs -> C-speed Timsort merge
    if not include_one and L and L[0] == 1:
        L = L[1:]
    return L

# ---------------------------------------------------------------------------
# SUM CENSUS
# ---------------------------------------------------------------------------
def sum_census_brute(L, B):
    """Method S1: transparent double loop, no parity/mod-16 structure used.
    Returns hits as (a, b, c) with a <= b, a + b = c, all in L, c <= B."""
    Ls = set(L)
    hits = []
    n = len(L)
    for i in range(n):
        a = L[i]
        rem = B - a
        for j in range(i, n):
            b = L[j]
            if b > rem: break
            if (a + b) in Ls:
                hits.append((a, b, a + b))
    return hits

def sum_census_lanes(L, B, tag='', do_ee=True, checkpoint=None, done=None):
    """Method S2: complete mod-16 lane decomposition.
      EE: a,b even (both 16 | a, 16 | b); c even.
      EO: e even, o odd; c odd; c == o (mod 16) since 16 | e.
      OO: a,b odd; c even 4-powerful => 16 | c => b == -a (mod 16).
    Every unordered pair of 4-powerful values falls in exactly one lane
    (parity), and within EO/OO the mod-16 constraint is FORCED (a + b = c
    4-powerful). EE pairs can never be coprime (gcd >= 16). Returns
    (hits, receipts) with hits = (a, b, c, lane) a <= b."""
    O = [x for x in L if x & 1]
    E = [x for x in L if not (x & 1)]
    Eset = set(E)
    oddres = (1, 3, 5, 7, 9, 11, 13, 15)
    obuck = {r: [o for o in O if (o & 15) == r] for r in oddres}
    hits = []
    receipts = {'EO': {}, 'OO': {}, 'EE': {}}

    def ckpt(payload):
        if checkpoint is None: return
        payload['elapsed'] = round(time.time() - T0, 1)
        with open(checkpoint, 'w') as fh:
            json.dump(payload, fh, indent=1)

    payload = {'bound': B, 'done_pairs': done if done else [], 'phase': 'start'}

    # ---- EO lane: (o, c) same mod-16 bucket, c > o, e = c - o in E ----
    nEO = 0
    for r in oddres:
        key = f'EO{r}'
        if done and key in done: continue
        bk = obuck[r]
        for ii in range(len(bk)):
            o = bk[ii]
            for c in bk[ii + 1:]:
                e = c - o
                if e > B: break
                nEO += 1
                if e in Eset:
                    hits.append((min(e, o), max(e, o), c, 'EO'))
        if done is not None:
            done.append(key)
            payload['done_pairs'] = done
            payload['phase'] = f'EO bucket {r}'
            ckpt(payload)
    receipts['EO'] = {'checks': nEO, 'buckets': {r: len(obuck[r]) for r in oddres}}

    # ---- OO lane: complementary mod-16 buckets ----
    nOO = 0
    for r in (1, 3, 5, 7):
        s = 16 - r
        key = f'OO{r}-{s}'
        if done and key in done: continue
        ba = obuck[r]; bb = obuck[s]
        for a in ba:
            for b in bb:
                c = a + b
                if c > B: break
                nOO += 1
                if c in Eset:
                    hits.append((min(a, b), max(a, b), c, 'OO'))
        if done is not None:
            done.append(key)
            payload['done_pairs'] = done
            payload['phase'] = f'OO pair {r}-{s}'
            ckpt(payload)
    receipts['OO'] = {'checks': nOO}

    # ---- EE lane: plain sweep (never coprime-relevant: gcd >= 16) ----
    nEE = 0
    if do_ee:
        key = 'EE'
        if not (done and key in done):
            nE = len(E)
            for i in range(nE):
                a = E[i]
                rem = B - a
                for j in range(i, nE):
                    b = E[j]
                    if b > rem: break
                    nEE += 1
                    if (a + b) in Eset:
                        hits.append((a, b, a + b, 'EE'))
            if done is not None:
                done.append(key)
                payload['done_pairs'] = done
                payload['phase'] = 'EE done'
                ckpt(payload)
    receipts['EE'] = {'checks': nEE}
    hits.sort()
    return hits, receipts

# ---------------------------------------------------------------------------
# VALIDATION PHASE
# ---------------------------------------------------------------------------
def phase_validate():
    log('--- V1: Lean-fold simulation vs fast predicate, all n <= 3000 ---')
    lp = {e: lean_prime(e) for e in range(0, 3001)}
    bad = [n for n in range(0, 3001) if lean_rpow(4, n, lp) != rpowerful(n, 4)]
    log(f'V1 disagreements (r=4): {len(bad)} -> {bad[:10]}')
    assert not bad
    bad3 = [n for n in range(0, 3001) if lean_rpow(3, n, lp) != rpowerful(n, 3)]
    assert not bad3
    log('V1 OK: literal Erdos939R4.lean fold == fast predicate on 0..3000 '
        '(r=3 and r=4). Edge: rpow4(0)=False, rpow4(1)=True (vacuous), '
        'rpow4(2)=False -> triple 1+1=2 fails.')

    log('--- V2: fast predicate vs sympy.factorint, all n <= 10^6 ---')
    from sympy import factorint
    bad = []
    for n in range(1, 10 ** 6 + 1):
        f = factorint(n)
        mine = (n == 1) or all(e >= 4 for e in f.values())
        if mine != rpowerful(n, 4):
            bad.append(n)
            if len(bad) > 5: break
    log(f'V2 disagreements: {len(bad)}')
    assert not bad
    log('V2 OK: independent factorizations agree on 1..10^6.')

    log('--- V3: DP generator vs brute predicate scan ---')
    for lim in (10 ** 4, 10 ** 5, 10 ** 6):
        L = gen4_dp(lim)
        brute = [n for n in range(1, lim + 1) if rpowerful(n, 4)]
        ok = (L == brute)
        log(f'V3 gen4_dp({lim}) == brute scan: {ok} (|L| = {len(L)}, '
            f'incl 1; excl-1 count {len(L) - 1})')
        assert ok
    log('V3 OK: Method-A layered-merge DP == brute predicate to 10^6.')

    log('--- V4: Lean K60 census row reproduction ---')
    got = gen4_dp(10 ** 4)
    log(f'V4 gen4_dp(10^4) == Erdos939R4 census row (25 values incl 1): '
        f'{got == LEAN_CENSUS_R4}')
    assert got == LEAN_CENSUS_R4
    c3 = [1, 8, 16, 27, 32, 64, 81, 125, 128, 216, 243, 256, 343, 432, 512,
          625, 648, 729, 864, 1000]
    log(f'V4b r=3 sanity: DP(10^4, r=3)... (skipped r=3 DP; brute below)')
    b3 = [n for n in range(1, 1001) if rpowerful(n, 3)]
    log(f'V4b brute r=3 <= 10^3 == battery939 c3 row: {b3 == c3}')
    assert b3 == c3

    log('--- V5: prior-hunt audit crosscheck (fourth powers vs true set) ---')
    fp = [m ** 4 for m in range(2, 1780) if m ** 4 <= 10 ** 13]
    L13 = gen4_dp(10 ** 13)
    log(f'V5 fourth powers <= 1e13: {len(fp)} (prior buggy engines: 1777); '
        f'true 4-powerful <= 1e13 incl 1: {len(L13)}, excl 1: {len(L13) - 1}; '
        f'32 in true list: {32 in L13}; 32 in fourth-power list: {32 in fp}')
    log('VALIDATE939_W66_ALL_OK')

# ---------------------------------------------------------------------------
# EMISSION
# ---------------------------------------------------------------------------
def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for blk in iter(lambda: fh.read(1 << 20), b''):
            h.update(blk)
    return h.hexdigest()

def emit_bound(dig, L, hits, receipts, extra=None, full_values=True):
    """Emit the witness-table files for bound 10^dig into table939_w66/."""
    os.makedirs(TAB, exist_ok=True)
    B = 10 ** dig
    tag = f'1e{dig}'
    # (a) value list — plain + delta + lean chunks
    if full_values:
        pvals = os.path.join(TAB, f'values939_{tag}.txt')
        with open(pvals, 'w') as fh:
            fh.write('\n'.join(str(v) for v in L) + '\n')
        pdel = os.path.join(TAB, f'values939_{tag}.delta.txt')
        with open(pdel, 'w') as fh:
            fh.write(f'# delta encoding of the sorted 4-powerful values <= {tag}\n'
                     f'# first value, then successive gaps (gap >= 13 at 1e4 scale)\n')
            fh.write(str(L[0]) + '\n')
            prev = L[0]
            for v in L[1:]:
                fh.write(str(v - prev) + '\n')
                prev = v
        plean = os.path.join(TAB, f'values939_{tag}.lean.txt')
        with open(plean, 'w') as fh:
            fh.write(f'-- Erdos939 W66 witness table: all 4-powerful values '
                     f'<= {tag} (rpow 4 n = true), {len(L)} values incl 1.\n'
                     f'-- 25 values per chunk, K60 census-row style.\n')
            for i in range(0, len(L), 25):
                chunk = L[i:i + 25]
                fh.write('[' + ', '.join(map(str, chunk)) + ']\n')
    # (b) sum-hit table with gcd column
    phits = os.path.join(TAB, f'sumhits939_{tag}.tsv')
    with open(phits, 'w') as fh:
        fh.write('# a\tb\tc\tgcd(a,b)\tlane\tpairwise_coprime\n')
        fh.write(f'# all rows: a+b=c, rpow4 a, rpow4 b, rpow4 c, c <= {tag}; '
                 f'gcd(a,b)=gcd(a,c)=gcd(b,c) (a+b=c lemma)\n')
        for (a, b, c, lane) in sorted(hits):
            g = math.gcd(a, b)
            fh.write(f'{a}\t{b}\t{c}\t{g}\t{lane}\t'
                     f'{"YES" if g == 1 else "no"}\n')
    # (c) coverage certificate
    cov = {
        'bound': tag, 'limit': B,
        'predicate': 'rpow 4 n = decide (1 <= n && divAll 4 n n) '
                     '(Erdos939R4.lean); n=1 vacuously true; emitted list '
                     'INCLUDES 1',
        'count_incl_1': len(L), 'count_excl_1': len(L) - (1 if L[0] == 1 else 0),
        'min_value': L[0], 'max_value': L[-1],
        'parity': {'odd': sum(1 for v in L if v & 1),
                   'even': sum(1 for v in L if not (v & 1))},
        'mod16_odd_buckets': {str(r): sum(1 for v in L if v & 1 and (v & 15) == r)
                               for r in (1, 3, 5, 7, 9, 11, 13, 15)},
        'per_decade_counts': {},
        'min_gap': None, 'min_gap_pair': None,
        'lane_receipts': receipts,
        'sum_hits_total': len(hits),
        'sum_hits_by_lane': {ln: sum(1 for h in hits if h[3] == ln)
                             for ln in ('EE', 'EO', 'OO')},
        'gcd_histogram_min': None,
        'zero_coprime_witnesses': None,
        'sorted_disjoint_ranges': [],
        'sha256': {},
    }
    for k in range(0, dig):
        lo, hi = 10 ** k, 10 ** (k + 1) - 1
        cov['per_decade_counts'][f'1e{k}'] = (bisect_right(L, hi) -
                                              bisect_right(L, 10 ** k - 1))
    gaps = [(L[i + 1] - L[i], L[i], L[i + 1]) for i in range(len(L) - 1)]
    mg = min(gaps)
    cov['min_gap'] = mg[0]; cov['min_gap_pair'] = [mg[1], mg[2]]
    # sorted disjoint range rows: [lo, hi, count] over consecutive value runs
    # with gap <= 100 (certificate of where the mass sits; checker validates)
    runs = []
    start = L[0]; prev = L[0]; cnt = 1
    for v in L[1:]:
        if v - prev <= 100:
            prev = v; cnt += 1
        else:
            runs.append([start, prev, cnt]); start = v; prev = v; cnt = 1
    runs.append([start, prev, cnt])
    cov['sorted_disjoint_ranges'] = runs
    gvals = {}
    for (a, b, c, lane) in hits:
        g = math.gcd(a, b)
        gvals[g] = gvals.get(g, 0) + 1
    cov['gcd_histogram'] = {str(k): v for k, v in sorted(gvals.items())}
    cov['min_hit_gcd'] = min(gvals) if gvals else None
    cov['zero_coprime_witnesses'] = (0 == sum(1 for g in gvals if g == 1))
    if full_values:
        cov['sha256'][f'values939_{tag}.txt'] = sha256(pvals)
        cov['sha256'][f'values939_{tag}.delta.txt'] = sha256(pdel)
        cov['sha256'][f'values939_{tag}.lean.txt'] = sha256(plean)
    cov['sha256'][f'sumhits939_{tag}.tsv'] = sha256(phits)
    if extra:
        cov.update(extra)
    pcov = os.path.join(TAB, f'coverage939_{tag}.json')
    with open(pcov, 'w') as fh:
        json.dump(cov, fh, indent=1, sort_keys=True)
    log(f'EMIT {tag}: values {"written" if full_values else "(skipped)"}; '
        f'sumhits {len(hits)} rows; coverage json at {pcov}')
    return cov

# ---------------------------------------------------------------------------
# CENSUS PHASE (dual method at 13/14; S2 beyond)
# ---------------------------------------------------------------------------
def phase_census(dig, dual=True, do_ee=True, full_values=True, emit=True):
    B = 10 ** dig
    t = time.time()
    L = gen4_dp(B)
    log(f'GEN 1e{dig}: |L| = {len(L)} incl 1 ({len(L) - 1} excl 1); '
        f'odd {sum(1 for v in L if v & 1)}, even {sum(1 for v in L if not (v & 1))}; '
        f'{time.time() - t:.1f}s')
    tagc = os.path.join(TAB, f'census939_1e{dig}.progress.json')
    hits2, receipts = sum_census_lanes(L, B, tag=f'1e{dig}', do_ee=do_ee,
                                        checkpoint=tagc, done=[])
    t2 = time.time() - t
    log(f'S2 lanes 1e{dig}: checks EO={receipts["EO"]["checks"]} '
        f'OO={receipts["OO"]["checks"]} EE={receipts["EE"]["checks"]}; '
        f'hits {len(hits2)} ({time.time() - t:.1f}s)')
    cop = [h for h in hits2 if math.gcd(h[0], h[1]) == 1]
    log(f'S2 gcd census 1e{dig}: sum-hits {len(hits2)}, coprime pairs {len(cop)} '
        f'-> ZERO pairwise-coprime triples: {not cop}')
    if dual:
        t = time.time()
        hits1 = sum_census_brute(L, B)
        s1 = sorted((a, b, c) for (a, b, c) in hits1)
        s2 = sorted((a, b, c) for (a, b, c, _) in hits2)
        agree = (s1 == s2)
        log(f'S1 transparent double-loop 1e{dig}: {len(hits1)} hits '
            f'({time.time() - t:.1f}s); S1 == S2 (EXACT): {agree}')
        if not agree:
            d1 = [x for x in s1 if x not in set(s2)][:8]
            d2 = [x for x in s2 if x not in set(s1)][:8]
            log(f'  S1-only: {d1}'); log(f'  S2-only: {d2}')
        assert agree, 'S1/S2 DISAGREEMENT — INVESTIGATE'
    # gcd-equality lemma receipt (gcd(a,b)=gcd(a,c)=gcd(b,c) for a+b=c)
    for (a, b, c, _) in hits2:
        g = math.gcd(a, b)
        assert g == math.gcd(a, c) == math.gcd(b, c)
    log('gcd-equality lemma verified on every hit (gcd(a,b)=gcd(a,c)=gcd(b,c)).')
    if emit:
        extra = {'methods': 'S2 mod-16 lanes' + (' + S1 transparent double-loop'
                 ' (EXACT agreement)' if dual else ''),
                 'engine': 'gen4_dp layered per-prime sorted-merge DP'}
        cov = emit_bound(dig, L, hits2, receipts, extra=extra,
                         full_values=full_values)
        log(f'coverage939_1e{dig}.json: min_hit_gcd={cov["min_hit_gcd"]}, '
            f'zero_coprime_witnesses={cov["zero_coprime_witnesses"]}')
    try:
        os.remove(tagc)
    except OSError:
        pass
    return L, hits2

# ---------------------------------------------------------------------------
# COUNTS PHASE (generation-only verification of the audit's count table)
# ---------------------------------------------------------------------------
def phase_counts():
    log('--- generation-only count verification (Method A DP) ---')
    for dig in (13, 14, 15, 16, 17, 18, 19):
        t = time.time()
        L = gen4_dp(10 ** dig)
        n = len(L)
        log(f'COUNT 1e{dig}: {n} incl 1 ({n - 1} excl 1); '
            f'{time.time() - t:.1f}s')
    log('audit claims (excl-1 convention): 11653@1e13, 40048@1e15, '
        '73698@1e16, 135058@1e17, 246652@1e18, 449087@1e19')

# ---------------------------------------------------------------------------
# BOX19 PHASE (background: the 1e19 EO/OO lanes with checkpoints/resume)
# ---------------------------------------------------------------------------
def phase_box19():
    B = 10 ** 19
    tagc = os.path.join(TAB, 'box19_progress.json')
    done = []
    if os.path.exists(tagc):
        with open(tagc) as fh:
            done = json.load(fh).get('done_pairs', [])
        log(f'resume: {len(done)} lane segments already done: {done}')
    t = time.time()
    L = gen4_dp(B)
    log(f'GEN 1e19: |L| = {len(L)} incl 1 ({len(L) - 1} excl 1); '
        f'{time.time() - t:.1f}s')
    hits, receipts = sum_census_lanes(L, B, tag='1e19', do_ee=False,
                                      checkpoint=tagc, done=done)
    cop = [h for h in hits if math.gcd(h[0], h[1]) == 1]
    log(f'BOX19 RESULT: sum-hits (EO+OO) = {len(hits)}; coprime = {len(cop)}; '
        f'ZERO pairwise-coprime triples <= 1e19: {not cop}')
    log(f'BOX19 receipts: EO checks {receipts["EO"]["checks"]}, '
        f'OO checks {receipts["OO"]["checks"]}')
    emit_bound(19, L, hits, receipts,
               extra={'methods': 'S2 mod-16 lanes EO+OO (EE skipped: never '
                       'coprime-relevant; gcd >= 16)',
                      'lane_definition_note': 'prior-hunt box (hunt939d) = EO+OO '
                       'lanes over the exclude-1 list; comparability note inside '
                       'STATUS939_W66E.md'},
               full_values=False)
    # still emit the plain value list for 1e19 (it is the box's member table)
    pvals = os.path.join(TAB, 'values939_1e19.txt')
    with open(pvals, 'w') as fh:
        fh.write('\n'.join(str(v) for v in L) + '\n')
    log(f'BOX19 value list written: {pvals} ({len(L)} values)')

# ---------------------------------------------------------------------------
def main():
    ph = sys.argv[1] if len(sys.argv) > 1 else 'help'
    if ph == 'validate':
        open_log('validate'); phase_validate()
    elif ph == 'census':
        dig = int(sys.argv[2]) if len(sys.argv) > 2 else 13
        dual = dig <= 13
        do_ee = dig <= 15
        open_log(f'census{dig}')
        phase_census(dig, dual=dual, do_ee=do_ee, full_values=True)
    elif ph == 'counts':
        open_log('counts'); phase_counts()
    elif ph == 'box19':
        open_log('box19'); phase_box19()
    else:
        print('usage: engine939_w66.py validate | census <13|14|15|16> | '
              'counts | box19')
    log(f'--- phase {ph} total {time.time() - T0:.1f}s ---')

if __name__ == '__main__':
    main()
