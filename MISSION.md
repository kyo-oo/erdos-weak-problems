# MISSION W67-142D — Erdős #142 DOUBTER/ENGINE LANE (Task ID: W67-142D)

## YOUR DISPOSITION: DOUBTER — break the KILLER's design or certify it.
Work in /home/z/waves/w67-p142d (branch w67-p142d). You do NOT author the
Lean kernel. Artifacts: problem142-ap-free/engine142/doubter/.

## THE FROZEN STATEMENT
"Let r_k(N) be the largest possible size of a subset of {1,...,N} that does
not contain any non-trivial k-term arithmetic progression. Prove an
asymptotic formula for r_k(N)." (Erdős, $10000, erdosproblems.com/142.)

## CONVENTION: non-trivial k-AP = a, a+d, ..., a+(k−1)d, d ≥ 1.
## KILLER's claims under audit (their worktree: origin/w67-p142k when pushed):
## (C1) T = ternary-digit-{0,1} numbers is 3-AP-free;
## (C2) r_3(3^k−1) ≥ 2^k − 1 (Cantor lower bound);
## (C3) r_k(N) ≤ (k−1)⌊N/k⌋ + (N mod k) (block upper bound);
## (C4) r_2(N) = 1 for N ≥ 2; (C5) exact r_3(N) for small N.

## YOUR ATTACKS (python + z3 + gmpy2 armed; 2 cores; cap runs ≤ 15 min each)

1. **THE INDEPENDENT CANTOR CERTIFICATION**: implement T_k yourself (k ≤ 8,
   3^k−1 = 6560, |T_8| = 256): verify 3-AP-freeness by DIRECT scan — for all
   x, z ∈ T_k, x < z with (x+z) even, check (x+z)/2 ∉ T_k. DUAL METHOD:
   digit-free (integer arithmetic) AND digit-list (base-3 digit vector)
   implementations must agree. Also verify the complement claim: the FIRST
   3-AP appearing when you add any single further element to T_8 ∩ [1,6560]
   (sanity that T is maximal-ish in its niche, not needed — but the
   no-3-AP claim is the KILL-claim: ANY break with exact reproduction).

2. **THE EXACT r_3(N) TABLE — branch-and-bound to N ≥ 30**: exhaustive 2^N
   scan dies at N ~ 26; implement a pruning B&B (choose/include-exclude with
   AP-completion pruning) or ILP (z3/pulp) — get exact r_3(N) for N ≤ 30.
   Cross-check N ≤ 12 against brute force (must agree 100%) + the known
   sequence (OEIS A065825: 1,2,2,3,4,4,4,4,4,5,5,6,6,6,6,7,8,8,8,8,9,...)
   — VERIFY against your own computation, do not trust the printed values.
   Bank doubter/r3_exact_table.json (N, r_3(N), one witness set).

3. **THE UPPER-BOUND STRESS**: the block bound r_3(N) ≤ 2⌊N/3⌋ + (N mod 3):
   verify it dominates the exact r_3(N) for all N ≤ 30 (any violation = KILL
   of the killer's lemma — reproduce exactly). Compute the true ratio
   r_3(N)·3/(2N) for N ≤ 30 — the approach-to-asymptotic honest intel.
   Also check the k=4, k=5 block bounds against exact r_4(N), r_5(N) for
   N ≤ 20 (B&B again). BANK the honest-scope table: for each k ∈ {3,4,5},
   the certified exact values + the block bound margin.

4. **THE k=2 EDGE AUDIT**: r_2(N) = 1 for N ≥ 2 — verify (trivially true
   under the d ≥ 1 convention; confirm no convention drift: under the
   alternative "non-trivial means k ≥ 3" convention the claim is void —
   state which convention the killer's kernel must pin; the kernel header
   must pin d ≥ 1).

5. **THE LOWER-BOUND FRONTIER (honest-scope intel)**: compare the Cantor
   bound 2^k−1 at N = 3^k−1 vs the TRUE r_3(3^k−1) for k ≤ 3 (N ≤ 26:
   exact from your B&B): the multiplicative gap (true_r3 / cantor) — bank
   it. This is the honest measure of how far the certified lower bound
   sits from truth at the certified scale.

6. **CI BATTERY**: kills.yml in YOUR worktree: add
   `- problem142-ap-free/**` to paths + a doubter job kernel-142d running
   `python3 problem142-ap-free/engine142/doubter/mirror_battery.py`
   (exit nonzero on ANY check failure — the battery re-runs checks 1–3
   end-to-end). Push branch w67-p142d, poll CI to green.

## LAWS
- Dual method on every census (two independent engines must agree exactly).
- Exact integer arithmetic only (no floats in verification claims).
- English only. Bank all artifacts, commit, push w67-p142d (token:
  /home/z/my-project/skill-bag/extracted/erdos-zipbag/secrets/ghtoken.txt).
- Report any BREAK with exact reproduction steps + the offending values.

## REPORT BACK: the Cantor certification verdict, the exact r_3 table
## (N ≤ 30) + witness, the block-bound verdict (any violation?), the
## k=4/k=5 exact frontier, the Cantor-vs-true gap, CI verdict,
## any BREAK with exact reproduction.
