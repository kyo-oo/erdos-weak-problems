# STATUS — #1063 frontier extended: n_15 = 4732, n_16 = 3213, n_17 = 1456

**S063 W62 volley, task 1-c (the guaranteed-kill executor).** Engine:
`engine_round2.py` (output `engine_round2_output.txt`, ALL GREEN, 1.2s).
Calibration law honored: the engine re-derives the certified tip
n_2..n_14 = (4, 6, 9, 12, 75, 30, 70, 56, 2403, 280, 3465, 210, 793) with the
same code path before extending.

## THE NEW CERTIFIED THEOREM (complete, unconditional)

$$n_{15}=4732,\qquad n_{16}=3213,\qquad n_{17}=1456 .$$

The certified frontier of #1063 now reads
$$n_k\ (k=2..17) = (4,6,9,12,75,30,70,56,2403,280,3465,210,793,4732,3213,1456).$$

Definition (COMPLETE_PROOF.md §0, verbatim corpus statement): n_k ≥ 2k is the
least n such that n−i divides C(n,k) for all but one 0 ≤ i < k; with
wcount(n,k) := #{i ∈ [0,k) : (n−i) | C(n,k)}, n_k = least n ≥ 2k with
wcount ≥ k−1.

## The certificate (per new row: witness + completeness, dual code paths)

| k | n_k | witness wcount | exempt i (n−i) | prime-power deficit (q, v_q(n−i), v_q(C)) | completeness sweep |
|---|-----|--------|------------|------------------------|--------------|
| 15 | 4732 | 14 = k−1 (exactly one miss) | i=7 (n−i=4725 = 3³·5²·7) | (3, 3, 1) | 4702 points, all wcount ≤ 13 |
| 16 | 3213 | 15 = k−1 (exactly one miss) | i=13 (n−i=3200 = 2⁷·5²) | (2, 7, 3) | 3181 points, all wcount ≤ 14 |
| 17 | 1456 | 16 = k−1 (exactly one miss) | i=11 (n−i=1445 = 5·17²) | (17, 2, 1) | 1422 points, all wcount ≤ 15 |

**Witness law:** at each n_k exactly one position i fails (the §3.7 force
analysis: the failure is an explicit prime-power deficit
v_q(n−i) > v_q(C(n_k,k)), exhibited in the table); all k−1 other positions
divide C(n_k, k).

**Completeness law:** every 2k ≤ n < n_k has wcount ≤ k−2 (at least two
misses) — the full sweep [2k, n_k) executed, 4702 + 3181 + 1422 = 9305
extension points.

**Dual independent code paths, point-by-point agreement (asserted on EVERY
swept point, 11,493 total incl. calibration):**
- Path A — the exact binomial: gmpy2.comb (GMP exact big integers), direct
  divisibility of the literal C(n,k) by each n−i.
- Path B — the valuation route (no binomial is ever formed):
  (n−i) | C(n,k) ⟺ for every prime q | (n−i),
  v_q(n−i) ≤ v_q(C(n,k)) with
  v_q(C(n,k)) = Σ_{j≥1} (⌊n/q^j⌋ − ⌊(n−k)/q^j⌋ − ⌊k/q^j⌋) (Legendre/Kummer).
  Both paths must agree at every single point — asserted; any disagreement
  would abort the engine.

## Calibration

n_2..n_14 re-derived by the same search path (dual-certified per point,
7218 points) and equal to the certified table of COMPLETE_PROOF.md §3.5 —
the engine reproduces the frontier tip n_14 = 793 before extending. GREEN.

## Honest scope

Each new value is a certified exact value of n_k at the stated k — "the
certified frontier extended to k = 17". No general-k law is claimed (the
corpus's open ask "Estimate n_k" remains open; Cambie's
n_k ≤ k·lcm(1..k−1) and Monier's n_k ≤ k! remain the corpus-recorded
bounds — both hold on the new rows: n_15/(15·lcm(1..14)) = 4732/5405400 ≈
8.8·10⁻⁴, etc.). The Lean-side chunk certificates (the §3.4 NO-OOM
501-element decide discipline) for the rows k = 15..17 are the optional
next step — the Python machine certificate above is complete as it stands.
