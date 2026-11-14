# STATUS — #1063 frontier extended: n_18 = 31110, n_19 = 612, n_20 = 67203

**W63 wave, task W63-C2 (dedicated wave agent).** Engines:
`engine_round3.py` (output `engine_round3_output.txt`, ALL GREEN, 15.5s — the
W62 dual-path discipline, extended) + `battery263.py` (output
`battery263_output.txt`, ALL GREEN, 2.2s — three disjoint second methods).

## THE NEW CERTIFIED THEOREM (complete, unconditional)

$$n_{18}=31110,\qquad n_{19}=612,\qquad n_{20}=67203 .$$

The certified frontier of #1063 now reads

$$n_k\ (k=2..20) = (4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456,31110,612,67203).$$

Definition (COMPLETE_PROOF.md §0, verbatim corpus statement): n_k ≥ 2k is the
least n such that n−i divides C(n,k) for all but one 0 ≤ i < k; with
wcount(n,k) := #{i ∈ [0,k) : (n−i) | C(n,k)}, n_k = least n ≥ 2k with
wcount ≥ k−1.

## The certificate (per new row: witness + completeness, dual code paths)

| k | n_k | witness wcount | exempt i (n−i) | prime-power deficits (q, v_q(n−i), v_q(C)) | completeness sweep |
|---|-----|--------|------------|------------------------|--------------|
| 18 | 31110 | 17 = k−1 (exactly one miss) | i=6 (n−i=31104 = 2⁷·3⁵) | (2, 7, 3), (3, 5, 3) | 31074 points, all wcount ≤ 16 |
| 19 | 612 | 18 = k−1 (exactly one miss) | i=4 (n−i=608 = 2⁵·19) | (2, 5, 3), (19, 1, 0) | 574 points, all wcount ≤ 17 |
| 20 | 67203 | 19 = k−1 (exactly one miss) | i=3 (n−i=67200 = 2⁷·3·5²·7) | (2, 7, 5), (5, 2, 1) | 67163 points, all wcount ≤ 18 |

**Witness law:** at each n_k exactly one position i fails (the §3.7 force
analysis: the failure is an explicit prime-power deficit
v_q(n−i) > v_q(C(n_k,k)), exhibited above — twice over at every exempt position);
all k−1 other positions divide C(n_k, k).

**Completeness law:** every 2k ≤ n < n_k has wcount ≤ k−2 (at least two
misses) — the full sweep [2k, n_k) executed: 31074 + 574 + 67163 = 98811
extension points.

**Dual independent code paths, point-by-point agreement (asserted on EVERY
swept point; this run: 214,154 points incl. calibration):**
- Path A — the exact binomial: gmpy2.comb (GMP exact big integers), direct
  divisibility of the literal C(n,k) by each n−i.
- Path B — the valuation route (no binomial is ever formed):
  (n−i) | C(n,k) ⟺ for every prime q | (n−i),
  v_q(n−i) ≤ v_q(C(n,k)) with
  v_q(C(n,k)) = Σ_{j≥1} (⌊n/q^j⌋ − ⌊(n−k)/q^j⌋ − ⌊k/q^j⌋) (Legendre/Kummer).
  Both paths must agree at every single point — asserted; any disagreement
  aborts the engine.
- Prime-table upgrade (necessary and documented): W62's Path B table covered
  primes ≤ 200 (safe only to n ~ 4·10⁴). Round 3 uses primes ≤ 300, so
  factor_small returns the TRUE factorization of every n−i for all swept
  n ≤ 67203 < 300² = 90000 — every Path B receipt is a literal prime-power
  statement.

## Independent second methods (battery263.py, ALL GREEN)

1. **stdlib math.comb** (CPython C implementation, no gmpy2/GMP): full
   witness + completeness recount of all nineteen rows k = 2..20 — GREEN,
   max wcount below each witness = k−2 exactly where required.
2. **Kummer carry-count route** (v_q(C(n,k)) = number of carries when adding
   k and n−k in base q — an algorithm disjoint from the Legendre floor sums):
   witness receipts re-derived (same exempt positions, same deficits), plus
   crosscheck against math.comb on boundary points (first/last 500 of every
   extension sweep) and 1000 pseudo-random interior points per new row —
   1953 + 574 + 1980 points, ZERO disagreements.
3. **sympy.binomial** (third big-int implementation) at the three new
   witnesses: wcount = k−1 each — GREEN.

## Calibration

n_2..n_17 re-derived by the same dual code path before any new row was
claimed (16,526 calibration points) and equal to the certified table
(4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456) — the engine
reproduces the W62 tip n_17 = 1456 before extending. GREEN.

## Bounds consistency (corpus-recorded, checked on the new rows)

Cambie n_k ≤ k·lcm(1..k−1): 31110 ≤ 220,540,320 (1.41·10⁻⁴); 612 ≤
232,792,560 (2.63·10⁻⁶); 67203 ≤ 4,655,851,200 (1.44·10⁻⁵). Monier
n_k ≤ k!: all hold (ratios ≤ 4.9·10⁻¹²). GREEN.

## Honest scope

Each new value is a certified exact value of n_k at the stated k — "the
certified frontier extended to k = 20". No general-k law is claimed (the
corpus's open ask "Estimate n_k" remains open). Empirical pattern observed on
all certified rows k ≥ 15 (NOT claimed as a law): the exempt position is
i = n_k mod k and n_k−i is a multiple of k (6 = 31110 mod 18, 31104 = 18·1728;
4 = 612 mod 19, 608 = 19·32; 3 = 67203 mod 20, 67200 = 20·3360). The
Lean-side chunk certificates (the §3.4 NO-OOM 501-element decide discipline)
for the rows k = 18..20 remain the optional next step — the Python machine
certificate above is complete as it stands. The scouting path that located
the rows (fast pruned Path-B scan; the pruning lemma "primes q > k are
auto-satisfied since v_q(k!) = 0 and n−i divides the numerator" was
decision-level crosschecked against the exact gmpy2 path on 1500 points per
k before use) is recorded in run263/ — the certified values themselves are
re-derived from scratch by engine_round3.py without trusting the scout.
