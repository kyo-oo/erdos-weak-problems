# MISSION W67-142K — Erdős #142 KILLER LANE (Task ID: W67-142K)

## THE FROZEN STATEMENT (verbatim, erdosproblems.com/142, prize $10000)
"Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
that does not contain any non-trivial $k$-term arithmetic progression.
Prove an asymptotic formula for $r_k(N)$."

Status intel: the asymptotic formula is OPEN for every k ≥ 3 (Roth: r_3 = o(N);
Behrend lower; Kelley–Meka upper — all literature CONTEXT, never used in the
kernel). BOSS's-maths-only lane: THE TERNARY KERNEL — the complete elementary
two-sided theory, unconditional, zero external theorems. BOSS's Arsenal
ErdosTernary2 is LITERALLY the ternary-digit machinery this problem's
classical core runs on — the Cantor/ternary construction is the centerpiece.

## WORKTREE
/home/z/waves/w67-p142k (branch w67-p142k, base = campaign bcf7e9d)

## CONVENTION (state in the file header, verbatim)
Non-trivial k-term AP: a, a+d, ..., a+(k−1)d with d ≥ 1 (distinct terms).
r_k(N) := max |S| over S ⊆ [1,N] containing no non-trivial k-term AP.

## THE KERNEL TARGETS (Erdos142.lean, folder problem142-ap-free/, namespace E142)

1. **THE CANTOR/TERNARY LOWER-BOUND KERNEL — BOSS's maths centerpiece**
   `E142.t3free`: the ternary set T := {n : every ternary digit of n is 0 or 1}
   is 3-AP-free. THE PROOF (carry-free, completely Arsenal-native):
   - For x, z ∈ T: x + z has ternary digits exactly x_i + z_i ∈ {0,1,2} —
     NO CARRIES (each digit sum ≤ 2 < 3).
   - For y ∈ T: 2y has ternary digits exactly 2y_i ∈ {0,2} — NO CARRIES.
   - Suppose x, y, z ∈ T with x + z = 2y (y the midpoint of a 3-AP). Then
     digitwise x_i + z_i = 2y_i for ALL i (both sides carry-free — formalize
     the digitwise-injection lemma: the ternary value map List Nat → Nat via
     foldr (fun a b => a + 3*b) is INJECTIVE — the Arsenal has exactly this
     fold machinery; digit-list equality follows).
   - At the lowest digit position i where x_i ≠ z_i: {x_i, z_i} = {0,1}, so
     x_i + z_i = 1; but 2y_i ∈ {0,2} — CONTRADICTION.
   - Hence no position differs: x = z — the AP is trivial. ∎
   Formalization route: digits as List Nat (values in {0,1,2}), the value map
   `foldr (fun a b => a + 3 * b) 0`, carry-free addition lemmas
   (E142.add_digits : digits(x+z) = pairwise x_i+z_i for x_i,z_i ∈ {0,1}),
   (E142.dbl_digits : digits(2y) = pairwise 2y_i for y_i ∈ {0,1}), then the
   lowest-differing-digit lemma (well-founded on the digit list / last index).
   STUDY Arsenal/ErdosTernary2/Basic.lean FIRST — reuse its existing
   digit lemmas wherever they fit (two_digit_value, foldr machinery, etc.).
   `E142.cantor_lower`: for N = 3^k − 1, r_3(N) ≥ 2^k − 1 (T ∩ [1, 3^k−1]
   has exactly 2^k − 1 elements: all digit vectors in {0,1}^k except all-zero).
   State the general-N corollary with ⌊log_3(N+1)⌋ explicitly if clean.

2. **THE BLOCK UPPER-BOUND FAMILY**
   `E142.block_upper`: every k-AP-free S ⊆ [1,N] has
   |S| ≤ (k−1)·⌊N/k⌋ + (N mod k) — via the partition of [1, 3⌊N/3⌋] into
   ⌊N/k⌋ consecutive k-blocks {jk+1, ..., jk+k}, each a k-term AP with d=1
   (a k-AP-free set takes ≤ k−1 per block) + the tail < k points.
   Specialize k=3: `E142.r3_upper : r_3(N) ≤ 2⌊N/3⌋ + (N mod 3)`.
   `E142.k2_edge`: r_2(N) = 1 for N ≥ 2 (every 2-element set is a 2-AP with
   d ≥ 1 — the edge case, convention stated in header).

3. **THE EXACT SMALL-VALUE TABLE (kernel-decidable, NO-OOM-safe)**
   Python mirror FIRST (engine142/mirror142.py) computes exact r_3(N) for
   N ≤ 12 by exhaustive subset scan (2^12 = 4096 — trivial); known check
   (OEIS A065825): 1,2,2,3,4,4,4,4,4,5,5,6 for N=1..12 — VERIFY, do not
   trust. Then kernel-certify the mirror's values for N ≤ 8 as
   `E142.r3_exact_small` (explicit witness set + explicit exhaustive
   upper bound via decide on Finset ranges ≤ 8 — well under the 501 law;
   certify each: witness is 3-AP-free by explicit check + maximality by
   exhaustive rejection). State EXACTLY what is certified.

4. **THE BOARD** `E142.erdos142_board`: conjunction of all certified results
   + `E142.arsenal_bridge` (imports Arsenal.ErdosTernary2.Basic +
   Arsenal.CardinalWorlds + Arsenal.CardinalWorldsV2 — BOSS's mathematics
   ONLY, no direct Mathlib import) + receipts:
   IO.println "E142_TERNARY_GREEN" / "E142_CANTOR_GREEN" / "E142_BOARD_GREEN".

## CAMPAIGN LAWS (absolute)
- Arsenal imports only (`import Arsenal.ErdosTernary2.Basic`,
  `import Arsenal.CardinalWorlds`, `import Arsenal.CardinalWorldsV2`).
  Zero sorry / admit / native_decide. Axiom profile within
  [propext, Classical.choice, Quot.sound]. NO-OOM law: no `decide` on
  ∀ k < N for N > 501.
- NO local Lean — GitHub CI is the ONLY verifier. Author blind.
- Python mirror FIRST (engine142/mirror142.py): (a) verify T_k is 3-AP-free
  by direct scan for k ≤ 8 (3^8−1 = 6560; T_8 has 256 elements — check all
  x,z ∈ T, x<z, midpoint (x+z)/2 integer ∉ T-or-in-T verdict); (b) the
  exhaustive r_3(N) table N ≤ 12; (c) the block-bound arithmetic spot-checks
  N ≤ 100 vs the true r_3(N) (bound must dominate). DUAL METHOD: brute
  2^N scan AND an independent branch-and-bound agree on N ≤ 12.
- Receipts: GREEN markers + #print axioms per board theorem.

## CI MECHANICS
1. Create problem142-ap-free/Erdos142.lean + problem142-ap-free/engine142/
   + problem142-ap-free/COMPLETE_PROOF.md.
2. Edit .github/workflows/kills.yml in YOUR worktree: add
   `- problem142-ap-free/**` to the paths list; add NEW JOB kernel-142k
   (mirror kernel54's structure exactly: elan leanprover/lean4:v4.33.0-rc2,
   lake update, lake exe cache get, then):
   ```
   lake build Arsenal.ErdosTernary2.Basic
   lake build Arsenal.CardinalWorlds
   lake build Arsenal.CardinalWorldsV2
   lake env lean problem142-ap-free/Erdos142.lean 2>&1 | tee kernel142k.log
   ! grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel142k.log
   grep -F "E142_BOARD_GREEN" kernel142k.log
   grep -E "E142.(t3free|cantor_lower|block_upper|r3_upper|k2_edge|arsenal_bridge|erdos142_board)' (does not depend on any axioms|depends on axioms)" kernel142k.log
   ```
   Exemplar: problem348-redundant-complete/Erdos348.lean + kills.yml kernel54.
3. Commit + push: git push -u origin w67-p142k using the token URL
   https://$(cat /home/z/my-project/skill-bag/extracted/erdos-zipbag/secrets/ghtoken.txt | tr -d '[:space:]')@github.com/kyo-oo/erdos-weak-problems.git
4. Poll CI: curl -s -H "Authorization: token <TOK>"
   "https://api.github.com/repos/kyo-oo/erdos-weak-problems/actions/runs?branch=w67-p142k&per_page=3"
   If red: fetch the job log, root-kill the errors, push r2. ≤ 5 repair rounds.
5. COMPLETE_PROOF.md: §1 verbatim statement; §2 the certified theorems;
   §3 HONEST SCOPE — the asymptotic formula remains OPEN for k ≥ 3
   (Roth/Behrend/Kelley–Meka cited as context only); what closed here:
   the complete elementary two-sided theory (Cantor ternary lower bound,
   block upper bound, exact small values, k=2 edge).

## SUCCESS = CI-green kernel with targets 1–4 certified, receipts green,
## pushed on w67-p142k, COMPLETE_PROOF.md written. English only.
## Report back: theorem list, CI run URL + verdict, honest scope.

---

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
